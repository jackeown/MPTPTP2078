%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t31_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 11.07s
% Output     : Refutation 11.07s
% Verified   : 
% Statistics : Number of formulae       :  339 ( 847 expanded)
%              Number of leaves         :   70 ( 372 expanded)
%              Depth                    :   16
%              Number of atoms          : 1365 (4694 expanded)
%              Number of equality atoms :  178 ( 840 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f263,f270,f284,f683,f813,f986,f1180,f1198,f1251,f1420,f1695,f2450,f2472,f2538,f2929,f3271,f3337,f3359,f3685,f3689,f3865,f5943,f6000,f6112,f8716,f11987,f11999,f12460,f12487,f12515,f19977,f21124,f21762,f22135,f22311,f32173,f127299,f139470,f176463,f179305,f181599,f181622,f194246,f260412,f260852])).

fof(f260852,plain,
    ( spl51_142
    | ~ spl51_122
    | ~ spl51_168 ),
    inference(avatar_split_clause,[],[f260851,f2536,f1412,f1693])).

fof(f1693,plain,
    ( spl51_142
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_142])])).

fof(f1412,plain,
    ( spl51_122
  <=> k1_xboole_0 = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_122])])).

fof(f2536,plain,
    ( spl51_168
  <=> ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_168])])).

fof(f260851,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_122
    | ~ spl51_168 ),
    inference(forward_demodulation,[],[f260850,f322])).

fof(f322,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f136,f85])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t1_boole)).

fof(f136,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',commutativity_k2_xboole_0)).

fof(f260850,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(k1_xboole_0,k1_tarski(sK3(sK0))))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_122
    | ~ spl51_168 ),
    inference(forward_demodulation,[],[f260849,f1413])).

fof(f1413,plain,
    ( k1_xboole_0 = sK4(sK0)
    | ~ spl51_122 ),
    inference(avatar_component_clause,[],[f1412])).

fof(f260849,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0)))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_122
    | ~ spl51_168 ),
    inference(forward_demodulation,[],[f260848,f322])).

fof(f260848,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(k1_xboole_0,k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_122
    | ~ spl51_168 ),
    inference(forward_demodulation,[],[f2537,f1413])).

fof(f2537,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_168 ),
    inference(avatar_component_clause,[],[f2536])).

fof(f260412,plain,
    ( spl51_168
    | ~ spl51_0
    | spl51_7
    | ~ spl51_548 ),
    inference(avatar_split_clause,[],[f194248,f12485,f282,f261,f2536])).

fof(f261,plain,
    ( spl51_0
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_0])])).

fof(f282,plain,
    ( spl51_7
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_7])])).

fof(f12485,plain,
    ( spl51_548
  <=> sP22(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_548])])).

fof(f194248,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_548 ),
    inference(subsumption_resolution,[],[f194247,f283])).

fof(f283,plain,
    ( k1_xboole_0 != sK0
    | ~ spl51_7 ),
    inference(avatar_component_clause,[],[f282])).

fof(f194247,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | k1_xboole_0 = sK0 )
    | ~ spl51_0
    | ~ spl51_548 ),
    inference(subsumption_resolution,[],[f181758,f262])).

fof(f262,plain,
    ( v1_finset_1(sK0)
    | ~ spl51_0 ),
    inference(avatar_component_clause,[],[f261])).

fof(f181758,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ v1_finset_1(sK0)
        | k1_xboole_0 = sK0 )
    | ~ spl51_548 ),
    inference(resolution,[],[f12486,f255])).

fof(f255,plain,(
    ! [X0,X5] :
      ( ~ sP22(X0)
      | r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,(
    ! [X0,X5] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0)
      | ~ sP22(X0) ) ),
    inference(general_splitting,[],[f123,f185_D])).

fof(f185,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | sP22(X0) ) ),
    inference(cnf_transformation,[],[f185_D])).

fof(f185_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_tarski(X2,sK2(X0))
          | ~ r2_hidden(X2,X0) )
    <=> ~ sP22(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP22])])).

fof(f123,plain,(
    ! [X2,X0,X5] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ! [X2] :
            ( r1_tarski(X2,sK2(X0))
            | ~ r2_hidden(X2,X0) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0
      | ( ! [X5] :
            ( ( ~ r1_tarski(sK5(X0,X5),X5)
              & r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))) )
            | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))) )
        & k1_xboole_0 != k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))
        & ( ( ! [X8] :
                ( r1_tarski(X8,sK6(X0))
                | ~ r2_hidden(X8,sK4(X0)) )
            & r2_hidden(sK6(X0),sK4(X0)) )
          | k1_xboole_0 = sK4(X0) )
        & r1_tarski(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | ( ! [X9] :
            ( ( ~ r1_tarski(sK7(X9),X9)
              & r2_hidden(sK7(X9),k1_xboole_0) )
            | ~ r2_hidden(X9,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f54,f59,f58,f57,f56,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ r2_hidden(X2,X0) )
          & r2_hidden(X1,X0) )
     => ( ! [X2] :
            ( r1_tarski(X2,sK2(X0))
            | ~ r2_hidden(X2,X0) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X3,X4] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X4,k1_tarski(X3))) )
              | ~ r2_hidden(X5,k2_xboole_0(X4,k1_tarski(X3))) )
          & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3))
          & ( ? [X7] :
                ( ! [X8] :
                    ( r1_tarski(X8,X7)
                    | ~ r2_hidden(X8,X4) )
                & r2_hidden(X7,X4) )
            | k1_xboole_0 = X4 )
          & r1_tarski(X4,X0)
          & r2_hidden(X3,X0) )
     => ( ! [X5] :
            ( ? [X6] :
                ( ~ r1_tarski(X6,X5)
                & r2_hidden(X6,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))) )
            | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))) )
        & k1_xboole_0 != k2_xboole_0(sK4(X0),k1_tarski(sK3(X0)))
        & ( ? [X7] :
              ( ! [X8] :
                  ( r1_tarski(X8,X7)
                  | ~ r2_hidden(X8,sK4(X0)) )
              & r2_hidden(X7,sK4(X0)) )
          | k1_xboole_0 = sK4(X0) )
        & r1_tarski(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X4,X3,X5,X0] :
      ( ? [X6] :
          ( ~ r1_tarski(X6,X5)
          & r2_hidden(X6,k2_xboole_0(X4,k1_tarski(X3))) )
     => ( ~ r1_tarski(sK5(X0,X5),X5)
        & r2_hidden(sK5(X0,X5),k2_xboole_0(X4,k1_tarski(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X4,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_tarski(X8,X7)
              | ~ r2_hidden(X8,X4) )
          & r2_hidden(X7,X4) )
     => ( ! [X8] :
            ( r1_tarski(X8,sK6(X0))
            | ~ r2_hidden(X8,X4) )
        & r2_hidden(sK6(X0),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X9] :
      ( ? [X10] :
          ( ~ r1_tarski(X10,X9)
          & r2_hidden(X10,k1_xboole_0) )
     => ( ~ r1_tarski(sK7(X9),X9)
        & r2_hidden(sK7(X9),k1_xboole_0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ r2_hidden(X2,X0) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0
      | ? [X3,X4] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X4,k1_tarski(X3))) )
              | ~ r2_hidden(X5,k2_xboole_0(X4,k1_tarski(X3))) )
          & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3))
          & ( ? [X7] :
                ( ! [X8] :
                    ( r1_tarski(X8,X7)
                    | ~ r2_hidden(X8,X4) )
                & r2_hidden(X7,X4) )
            | k1_xboole_0 = X4 )
          & r1_tarski(X4,X0)
          & r2_hidden(X3,X0) )
      | ( ! [X9] :
            ( ? [X10] :
                ( ~ r1_tarski(X10,X9)
                & r2_hidden(X10,k1_xboole_0) )
            | ~ r2_hidden(X9,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X10,X9)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X8,X7)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X10,X9)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X8,X7)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X1,X2] :
            ( ( ~ ( ! [X3] :
                      ~ ( ! [X4] :
                            ( r2_hidden(X4,X2)
                           => r1_tarski(X4,X3) )
                        & r2_hidden(X3,X2) )
                  & k1_xboole_0 != X2 )
              & r1_tarski(X2,X0)
              & r2_hidden(X1,X0) )
           => ~ ( ! [X5] :
                    ~ ( ! [X6] :
                          ( r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1)))
                         => r1_tarski(X6,X5) )
                      & r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
                & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1)) ) )
        & ~ ( ! [X7] :
                ~ ( ! [X8] :
                      ( r2_hidden(X8,k1_xboole_0)
                     => r1_tarski(X8,X7) )
                  & r2_hidden(X7,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X10,X9) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ! [X3,X4] :
            ( ( ~ ( ! [X5] :
                      ~ ( ! [X6] :
                            ( r2_hidden(X6,X4)
                           => r1_tarski(X6,X5) )
                        & r2_hidden(X5,X4) )
                  & k1_xboole_0 != X4 )
              & r1_tarski(X4,X0)
              & r2_hidden(X3,X0) )
           => ~ ( ! [X7] :
                    ~ ( ! [X8] :
                          ( r2_hidden(X8,k2_xboole_0(X4,k1_tarski(X3)))
                         => r1_tarski(X8,X7) )
                      & r2_hidden(X7,k2_xboole_0(X4,k1_tarski(X3))) )
                & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3)) ) )
        & ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k1_xboole_0)
                     => r1_tarski(X2,X1) )
                  & r2_hidden(X1,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X10,X9) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',s2_finset_1__e6_54__finset_1)).

fof(f12486,plain,
    ( sP22(sK0)
    | ~ spl51_548 ),
    inference(avatar_component_clause,[],[f12485])).

fof(f194246,plain,
    ( spl51_162
    | ~ spl51_0
    | spl51_7
    | ~ spl51_542 ),
    inference(avatar_split_clause,[],[f181756,f12458,f282,f261,f2470])).

fof(f2470,plain,
    ( spl51_162
  <=> ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_162])])).

fof(f12458,plain,
    ( spl51_542
  <=> sP17(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_542])])).

fof(f181756,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_542 ),
    inference(subsumption_resolution,[],[f181755,f283])).

fof(f181755,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | k1_xboole_0 = sK0 )
    | ~ spl51_0
    | ~ spl51_542 ),
    inference(subsumption_resolution,[],[f181754,f262])).

fof(f181754,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ v1_finset_1(sK0)
        | k1_xboole_0 = sK0 )
    | ~ spl51_542 ),
    inference(resolution,[],[f12459,f254])).

fof(f254,plain,(
    ! [X0,X5] :
      ( ~ sP17(X0)
      | ~ r1_tarski(sK5(X0,X5),X5)
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f176])).

fof(f176,plain,(
    ! [X0,X5] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(sK5(X0,X5),X5)
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0)
      | ~ sP17(X0) ) ),
    inference(general_splitting,[],[f126,f175_D])).

fof(f175,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | sP17(X0) ) ),
    inference(cnf_transformation,[],[f175_D])).

fof(f175_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_tarski(X2,sK2(X0))
          | ~ r2_hidden(X2,X0) )
    <=> ~ sP17(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP17])])).

fof(f126,plain,(
    ! [X2,X0,X5] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK5(X0,X5),X5)
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f12459,plain,
    ( sP17(sK0)
    | ~ spl51_542 ),
    inference(avatar_component_clause,[],[f12458])).

fof(f181622,plain,
    ( spl51_310
    | ~ spl51_1310 ),
    inference(avatar_split_clause,[],[f181605,f181597,f5941])).

fof(f5941,plain,
    ( spl51_310
  <=> sK3(sK0) = sK5(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_310])])).

fof(f181597,plain,
    ( spl51_1310
  <=> r2_hidden(sK5(sK0,sK3(sK0)),k1_tarski(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_1310])])).

fof(f181605,plain,
    ( sK3(sK0) = sK5(sK0,sK3(sK0))
    | ~ spl51_1310 ),
    inference(resolution,[],[f181598,f163])).

fof(f163,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK11(X0,X1) != X0
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( sK11(X0,X1) = X0
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK11(X0,X1) != X0
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( sK11(X0,X1) = X0
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',d1_tarski)).

fof(f181598,plain,
    ( r2_hidden(sK5(sK0,sK3(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_1310 ),
    inference(avatar_component_clause,[],[f181597])).

fof(f181599,plain,
    ( spl51_1310
    | ~ spl51_622
    | spl51_1291 ),
    inference(avatar_split_clause,[],[f181592,f179303,f21122,f181597])).

fof(f21122,plain,
    ( spl51_622
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK5(sK0,X0),sK4(sK0))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_622])])).

fof(f179303,plain,
    ( spl51_1291
  <=> ~ r2_hidden(sK5(sK0,sK3(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_1291])])).

fof(f181592,plain,
    ( r2_hidden(sK5(sK0,sK3(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_622
    | ~ spl51_1291 ),
    inference(subsumption_resolution,[],[f105845,f179304])).

fof(f179304,plain,
    ( ~ r2_hidden(sK5(sK0,sK3(sK0)),sK4(sK0))
    | ~ spl51_1291 ),
    inference(avatar_component_clause,[],[f179303])).

fof(f105845,plain,
    ( r2_hidden(sK5(sK0,sK3(sK0)),sK4(sK0))
    | r2_hidden(sK5(sK0,sK3(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_622 ),
    inference(resolution,[],[f21123,f341])).

fof(f341,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f164,f162])).

fof(f162,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f164,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
              & ~ r2_hidden(sK12(X0,X1,X2),X0) )
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( r2_hidden(sK12(X0,X1,X2),X1)
            | r2_hidden(sK12(X0,X1,X2),X0)
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            & ~ r2_hidden(sK12(X0,X1,X2),X0) )
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( r2_hidden(sK12(X0,X1,X2),X1)
          | r2_hidden(sK12(X0,X1,X2),X0)
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',d3_xboole_0)).

fof(f21123,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK5(sK0,X0),sK4(sK0))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_622 ),
    inference(avatar_component_clause,[],[f21122])).

fof(f179305,plain,
    ( ~ spl51_1291
    | ~ spl51_162
    | ~ spl51_1276 ),
    inference(avatar_split_clause,[],[f179152,f176461,f2470,f179303])).

fof(f176461,plain,
    ( spl51_1276
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0))
        | r1_tarski(X0,sK3(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_1276])])).

fof(f179152,plain,
    ( ~ r2_hidden(sK5(sK0,sK3(sK0)),sK4(sK0))
    | ~ spl51_162
    | ~ spl51_1276 ),
    inference(subsumption_resolution,[],[f179149,f341])).

fof(f179149,plain,
    ( ~ r2_hidden(sK5(sK0,sK3(sK0)),sK4(sK0))
    | ~ r2_hidden(sK3(sK0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
    | ~ spl51_162
    | ~ spl51_1276 ),
    inference(resolution,[],[f176462,f2471])).

fof(f2471,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_162 ),
    inference(avatar_component_clause,[],[f2470])).

fof(f176462,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK3(sK0))
        | ~ r2_hidden(X0,sK4(sK0)) )
    | ~ spl51_1276 ),
    inference(avatar_component_clause,[],[f176461])).

fof(f176463,plain,
    ( spl51_1276
    | ~ spl51_246
    | ~ spl51_1004 ),
    inference(avatar_split_clause,[],[f139472,f139468,f3687,f176461])).

fof(f3687,plain,
    ( spl51_246
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK4(sK0))
        | ~ r1_tarski(sK6(sK0),X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_246])])).

fof(f139468,plain,
    ( spl51_1004
  <=> r1_tarski(sK6(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_1004])])).

fof(f139472,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0))
        | r1_tarski(X0,sK3(sK0)) )
    | ~ spl51_246
    | ~ spl51_1004 ),
    inference(resolution,[],[f139469,f3688])).

fof(f3688,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK6(sK0),X1)
        | ~ r2_hidden(X0,sK4(sK0))
        | r1_tarski(X0,X1) )
    | ~ spl51_246 ),
    inference(avatar_component_clause,[],[f3687])).

fof(f139469,plain,
    ( r1_tarski(sK6(sK0),sK3(sK0))
    | ~ spl51_1004 ),
    inference(avatar_component_clause,[],[f139468])).

fof(f139470,plain,
    ( spl51_1004
    | ~ spl51_224
    | spl51_637
    | ~ spl51_972 ),
    inference(avatar_split_clause,[],[f139259,f127297,f22309,f3351,f139468])).

fof(f3351,plain,
    ( spl51_224
  <=> r2_hidden(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_224])])).

fof(f22309,plain,
    ( spl51_637
  <=> ~ r1_tarski(sK3(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_637])])).

fof(f127297,plain,
    ( spl51_972
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK3(sK0))
        | r1_tarski(sK3(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_972])])).

fof(f139259,plain,
    ( r1_tarski(sK6(sK0),sK3(sK0))
    | ~ spl51_224
    | ~ spl51_637
    | ~ spl51_972 ),
    inference(subsumption_resolution,[],[f138636,f22310])).

fof(f22310,plain,
    ( ~ r1_tarski(sK3(sK0),sK6(sK0))
    | ~ spl51_637 ),
    inference(avatar_component_clause,[],[f22309])).

fof(f138636,plain,
    ( r1_tarski(sK6(sK0),sK3(sK0))
    | r1_tarski(sK3(sK0),sK6(sK0))
    | ~ spl51_224
    | ~ spl51_972 ),
    inference(resolution,[],[f127298,f3352])).

fof(f3352,plain,
    ( r2_hidden(sK6(sK0),sK0)
    | ~ spl51_224 ),
    inference(avatar_component_clause,[],[f3351])).

fof(f127298,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK3(sK0))
        | r1_tarski(sK3(sK0),X0) )
    | ~ spl51_972 ),
    inference(avatar_component_clause,[],[f127297])).

fof(f127299,plain,
    ( spl51_972
    | ~ spl51_66
    | ~ spl51_252 ),
    inference(avatar_split_clause,[],[f12001,f3863,f681,f127297])).

fof(f681,plain,
    ( spl51_66
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_66])])).

fof(f3863,plain,
    ( spl51_252
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0)
        | r1_tarski(X0,X1)
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_252])])).

fof(f12001,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK3(sK0))
        | r1_tarski(sK3(sK0),X0) )
    | ~ spl51_66
    | ~ spl51_252 ),
    inference(resolution,[],[f682,f3864])).

fof(f3864,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,X1)
        | r1_tarski(X1,X0) )
    | ~ spl51_252 ),
    inference(avatar_component_clause,[],[f3863])).

fof(f682,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl51_66 ),
    inference(avatar_component_clause,[],[f681])).

fof(f32173,plain,
    ( spl51_114
    | ~ spl51_0
    | spl51_7
    | spl51_123
    | spl51_125 ),
    inference(avatar_split_clause,[],[f32172,f1415,f1409,f282,f261,f1249])).

fof(f1249,plain,
    ( spl51_114
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_114])])).

fof(f1409,plain,
    ( spl51_123
  <=> k1_xboole_0 != sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_123])])).

fof(f1415,plain,
    ( spl51_125
  <=> ~ r2_hidden(sK6(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_125])])).

fof(f32172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_123
    | ~ spl51_125 ),
    inference(subsumption_resolution,[],[f6473,f1416])).

fof(f1416,plain,
    ( ~ r2_hidden(sK6(sK0),sK4(sK0))
    | ~ spl51_125 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f6473,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK6(sK0),sK4(sK0))
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_123 ),
    inference(subsumption_resolution,[],[f685,f1410])).

fof(f1410,plain,
    ( k1_xboole_0 != sK4(sK0)
    | ~ spl51_123 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f685,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK6(sK0),sK4(sK0))
        | k1_xboole_0 = sK4(sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f684,f283])).

fof(f684,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK0
        | r2_hidden(sK6(sK0),sK4(sK0))
        | k1_xboole_0 = sK4(sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0 ),
    inference(resolution,[],[f252,f262])).

fof(f252,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0),sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | r1_tarski(X2,sK2(X0)) ) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0),sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f22311,plain,
    ( ~ spl51_637
    | ~ spl51_162
    | ~ spl51_174
    | ~ spl51_632 ),
    inference(avatar_split_clause,[],[f22229,f22133,f2927,f2470,f22309])).

fof(f2927,plain,
    ( spl51_174
  <=> ! [X0] : r2_hidden(sK6(sK0),k2_xboole_0(sK4(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_174])])).

fof(f22133,plain,
    ( spl51_632
  <=> sK3(sK0) = sK5(sK0,sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_632])])).

fof(f22229,plain,
    ( ~ r1_tarski(sK3(sK0),sK6(sK0))
    | ~ spl51_162
    | ~ spl51_174
    | ~ spl51_632 ),
    inference(subsumption_resolution,[],[f22226,f2928])).

fof(f2928,plain,
    ( ! [X0] : r2_hidden(sK6(sK0),k2_xboole_0(sK4(sK0),X0))
    | ~ spl51_174 ),
    inference(avatar_component_clause,[],[f2927])).

fof(f22226,plain,
    ( ~ r1_tarski(sK3(sK0),sK6(sK0))
    | ~ r2_hidden(sK6(sK0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
    | ~ spl51_162
    | ~ spl51_632 ),
    inference(superposition,[],[f2471,f22134])).

fof(f22134,plain,
    ( sK3(sK0) = sK5(sK0,sK6(sK0))
    | ~ spl51_632 ),
    inference(avatar_component_clause,[],[f22133])).

fof(f22135,plain,
    ( spl51_632
    | ~ spl51_630 ),
    inference(avatar_split_clause,[],[f22042,f21760,f22133])).

fof(f21760,plain,
    ( spl51_630
  <=> r2_hidden(sK5(sK0,sK6(sK0)),k1_tarski(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_630])])).

fof(f22042,plain,
    ( sK3(sK0) = sK5(sK0,sK6(sK0))
    | ~ spl51_630 ),
    inference(resolution,[],[f21761,f163])).

fof(f21761,plain,
    ( r2_hidden(sK5(sK0,sK6(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_630 ),
    inference(avatar_component_clause,[],[f21760])).

fof(f21762,plain,
    ( spl51_630
    | ~ spl51_174
    | spl51_429
    | ~ spl51_622 ),
    inference(avatar_split_clause,[],[f21395,f21122,f8714,f2927,f21760])).

fof(f8714,plain,
    ( spl51_429
  <=> ~ r2_hidden(sK5(sK0,sK6(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_429])])).

fof(f21395,plain,
    ( r2_hidden(sK5(sK0,sK6(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_174
    | ~ spl51_429
    | ~ spl51_622 ),
    inference(subsumption_resolution,[],[f21132,f8715])).

fof(f8715,plain,
    ( ~ r2_hidden(sK5(sK0,sK6(sK0)),sK4(sK0))
    | ~ spl51_429 ),
    inference(avatar_component_clause,[],[f8714])).

fof(f21132,plain,
    ( r2_hidden(sK5(sK0,sK6(sK0)),sK4(sK0))
    | r2_hidden(sK5(sK0,sK6(sK0)),k1_tarski(sK3(sK0)))
    | ~ spl51_174
    | ~ spl51_622 ),
    inference(resolution,[],[f21123,f2928])).

fof(f21124,plain,
    ( spl51_622
    | ~ spl51_168 ),
    inference(avatar_split_clause,[],[f20922,f2536,f21122])).

fof(f20922,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK5(sK0,X0),sK4(sK0))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_168 ),
    inference(resolution,[],[f2537,f166])).

fof(f166,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f19977,plain,
    ( spl51_158
    | ~ spl51_0
    | spl51_7
    | spl51_123
    | ~ spl51_554 ),
    inference(avatar_split_clause,[],[f12519,f12513,f1409,f282,f261,f2448])).

fof(f2448,plain,
    ( spl51_158
  <=> ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_158])])).

fof(f12513,plain,
    ( spl51_554
  <=> sP29(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_554])])).

fof(f12519,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_123
    | ~ spl51_554 ),
    inference(subsumption_resolution,[],[f12518,f283])).

fof(f12518,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | k1_xboole_0 = sK0 )
    | ~ spl51_0
    | ~ spl51_123
    | ~ spl51_554 ),
    inference(subsumption_resolution,[],[f12517,f262])).

fof(f12517,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | ~ v1_finset_1(sK0)
        | k1_xboole_0 = sK0 )
    | ~ spl51_123
    | ~ spl51_554 ),
    inference(subsumption_resolution,[],[f12516,f1410])).

fof(f12516,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | k1_xboole_0 = sK4(sK0)
        | ~ v1_finset_1(sK0)
        | k1_xboole_0 = sK0 )
    | ~ spl51_554 ),
    inference(resolution,[],[f12514,f256])).

fof(f256,plain,(
    ! [X0,X8] :
      ( ~ sP29(X0)
      | r1_tarski(X8,sK6(X0))
      | ~ r2_hidden(X8,sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,(
    ! [X0,X8] :
      ( k1_xboole_0 = X0
      | r1_tarski(X8,sK6(X0))
      | ~ r2_hidden(X8,sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0)
      | ~ sP29(X0) ) ),
    inference(general_splitting,[],[f117,f199_D])).

fof(f199,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | sP29(X0) ) ),
    inference(cnf_transformation,[],[f199_D])).

fof(f199_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_tarski(X2,sK2(X0))
          | ~ r2_hidden(X2,X0) )
    <=> ~ sP29(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP29])])).

fof(f117,plain,(
    ! [X2,X0,X8] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r1_tarski(X8,sK6(X0))
      | ~ r2_hidden(X8,sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f12514,plain,
    ( sP29(sK0)
    | ~ spl51_554 ),
    inference(avatar_component_clause,[],[f12513])).

fof(f12515,plain,
    ( ~ spl51_109
    | spl51_554
    | ~ spl51_64 ),
    inference(avatar_split_clause,[],[f11850,f675,f12513,f1166])).

fof(f1166,plain,
    ( spl51_109
  <=> ~ r2_hidden(sK1(sK2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_109])])).

fof(f675,plain,
    ( spl51_64
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_64])])).

fof(f11850,plain,
    ( sP29(sK0)
    | ~ r2_hidden(sK1(sK2(sK0)),sK0)
    | ~ spl51_64 ),
    inference(resolution,[],[f676,f467])).

fof(f467,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK2(X9),sK0)
      | sP29(X9)
      | ~ r2_hidden(sK1(sK2(X9)),X9) ) ),
    inference(resolution,[],[f199,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1(X1),X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ! [X1] :
        ( ( ~ r1_tarski(sK1(X1),X1)
          & r2_hidden(sK1(X1),sK0) )
        | ~ r2_hidden(X1,sK0) )
    & v6_ordinal1(sK0)
    & k1_xboole_0 != sK0
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X2,X1)
                & r2_hidden(X2,X0) )
            | ~ r2_hidden(X1,X0) )
        & v6_ordinal1(X0)
        & k1_xboole_0 != X0
        & v1_finset_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & r2_hidden(X2,sK0) )
          | ~ r2_hidden(X1,sK0) )
      & v6_ordinal1(sK0)
      & k1_xboole_0 != sK0
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X1),X1)
        & r2_hidden(sK1(X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & r2_hidden(X2,X0) )
          | ~ r2_hidden(X1,X0) )
      & v6_ordinal1(X0)
      & k1_xboole_0 != X0
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,X0)
                   => r1_tarski(X2,X1) )
                & r2_hidden(X1,X0) )
          & v6_ordinal1(X0)
          & k1_xboole_0 != X0
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X0)
                 => r1_tarski(X2,X1) )
              & r2_hidden(X1,X0) )
        & v6_ordinal1(X0)
        & k1_xboole_0 != X0
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t31_finset_1)).

fof(f676,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl51_64 ),
    inference(avatar_component_clause,[],[f675])).

fof(f12487,plain,
    ( ~ spl51_109
    | spl51_548
    | ~ spl51_64 ),
    inference(avatar_split_clause,[],[f11847,f675,f12485,f1166])).

fof(f11847,plain,
    ( sP22(sK0)
    | ~ r2_hidden(sK1(sK2(sK0)),sK0)
    | ~ spl51_64 ),
    inference(resolution,[],[f676,f444])).

fof(f444,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK2(X9),sK0)
      | sP22(X9)
      | ~ r2_hidden(sK1(sK2(X9)),X9) ) ),
    inference(resolution,[],[f185,f83])).

fof(f12460,plain,
    ( ~ spl51_109
    | spl51_542
    | ~ spl51_64 ),
    inference(avatar_split_clause,[],[f11844,f675,f12458,f1166])).

fof(f11844,plain,
    ( sP17(sK0)
    | ~ r2_hidden(sK1(sK2(sK0)),sK0)
    | ~ spl51_64 ),
    inference(resolution,[],[f676,f414])).

fof(f414,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK2(X9),sK0)
      | sP17(X9)
      | ~ r2_hidden(sK1(sK2(X9)),X9) ) ),
    inference(resolution,[],[f175,f83])).

fof(f11999,plain,
    ( spl51_114
    | ~ spl51_0
    | spl51_7
    | spl51_67 ),
    inference(avatar_split_clause,[],[f11989,f678,f282,f261,f1249])).

fof(f678,plain,
    ( spl51_67
  <=> ~ r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_67])])).

fof(f11989,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_67 ),
    inference(subsumption_resolution,[],[f563,f679])).

fof(f679,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | ~ spl51_67 ),
    inference(avatar_component_clause,[],[f678])).

fof(f563,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK3(sK0),sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f562,f283])).

fof(f562,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK0
        | r2_hidden(sK3(sK0),sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0 ),
    inference(resolution,[],[f250,f262])).

fof(f250,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0)
      | r1_tarski(X2,sK2(X0)) ) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f11987,plain,
    ( ~ spl51_64
    | ~ spl51_114 ),
    inference(avatar_contradiction_clause,[],[f11986])).

fof(f11986,plain,
    ( $false
    | ~ spl51_64
    | ~ spl51_114 ),
    inference(subsumption_resolution,[],[f11833,f676])).

fof(f11833,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl51_114 ),
    inference(subsumption_resolution,[],[f8812,f82])).

fof(f82,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8812,plain,
    ( ~ r2_hidden(sK1(sK2(sK0)),sK0)
    | ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl51_114 ),
    inference(resolution,[],[f1250,f83])).

fof(f1250,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK2(sK0))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl51_114 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f8716,plain,
    ( ~ spl51_429
    | ~ spl51_158
    | ~ spl51_162
    | ~ spl51_174 ),
    inference(avatar_split_clause,[],[f8709,f2927,f2470,f2448,f8714])).

fof(f8709,plain,
    ( ~ r2_hidden(sK5(sK0,sK6(sK0)),sK4(sK0))
    | ~ spl51_158
    | ~ spl51_162
    | ~ spl51_174 ),
    inference(subsumption_resolution,[],[f6510,f2928])).

fof(f6510,plain,
    ( ~ r2_hidden(sK5(sK0,sK6(sK0)),sK4(sK0))
    | ~ r2_hidden(sK6(sK0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
    | ~ spl51_158
    | ~ spl51_162 ),
    inference(resolution,[],[f2449,f2471])).

fof(f2449,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0)) )
    | ~ spl51_158 ),
    inference(avatar_component_clause,[],[f2448])).

fof(f6112,plain,
    ( ~ spl51_162
    | ~ spl51_310 ),
    inference(avatar_contradiction_clause,[],[f6111])).

fof(f6111,plain,
    ( $false
    | ~ spl51_162
    | ~ spl51_310 ),
    inference(subsumption_resolution,[],[f6110,f341])).

fof(f6110,plain,
    ( ~ r2_hidden(sK3(sK0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
    | ~ spl51_162
    | ~ spl51_310 ),
    inference(subsumption_resolution,[],[f6109,f385])).

fof(f385,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f141,f134])).

fof(f134,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',reflexivity_r3_xboole_0)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X0,X1)
      | r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',d9_xboole_0)).

fof(f6109,plain,
    ( ~ r1_tarski(sK3(sK0),sK3(sK0))
    | ~ r2_hidden(sK3(sK0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
    | ~ spl51_162
    | ~ spl51_310 ),
    inference(superposition,[],[f2471,f5942])).

fof(f5942,plain,
    ( sK3(sK0) = sK5(sK0,sK3(sK0))
    | ~ spl51_310 ),
    inference(avatar_component_clause,[],[f5941])).

fof(f6000,plain,
    ( spl51_7
    | ~ spl51_226 ),
    inference(avatar_contradiction_clause,[],[f5999])).

fof(f5999,plain,
    ( $false
    | ~ spl51_7
    | ~ spl51_226 ),
    inference(subsumption_resolution,[],[f5994,f283])).

fof(f5994,plain,
    ( k1_xboole_0 = sK0
    | ~ spl51_226 ),
    inference(resolution,[],[f3358,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t6_boole)).

fof(f3358,plain,
    ( v1_xboole_0(sK0)
    | ~ spl51_226 ),
    inference(avatar_component_clause,[],[f3357])).

fof(f3357,plain,
    ( spl51_226
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_226])])).

fof(f5943,plain,
    ( spl51_310
    | ~ spl51_244 ),
    inference(avatar_split_clause,[],[f4806,f3683,f5941])).

fof(f3683,plain,
    ( spl51_244
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | sK3(sK0) = sK5(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_244])])).

fof(f4806,plain,
    ( sK3(sK0) = sK5(sK0,sK3(sK0))
    | ~ spl51_244 ),
    inference(resolution,[],[f3684,f162])).

fof(f3684,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | sK3(sK0) = sK5(sK0,X0) )
    | ~ spl51_244 ),
    inference(avatar_component_clause,[],[f3683])).

fof(f3865,plain,
    ( spl51_252
    | ~ spl51_94 ),
    inference(avatar_split_clause,[],[f987,f984,f3863])).

fof(f984,plain,
    ( spl51_94
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0)
        | r3_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_94])])).

fof(f987,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0)
        | r1_tarski(X0,X1)
        | r1_tarski(X1,X0) )
    | ~ spl51_94 ),
    inference(resolution,[],[f985,f141])).

fof(f985,plain,
    ( ! [X0,X1] :
        ( r3_xboole_0(X1,X0)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl51_94 ),
    inference(avatar_component_clause,[],[f984])).

fof(f3689,plain,
    ( spl51_246
    | ~ spl51_158 ),
    inference(avatar_split_clause,[],[f2451,f2448,f3687])).

fof(f2451,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK4(sK0))
        | ~ r1_tarski(sK6(sK0),X1)
        | r1_tarski(X0,X1) )
    | ~ spl51_158 ),
    inference(resolution,[],[f2449,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t1_xboole_1)).

fof(f3685,plain,
    ( spl51_244
    | ~ spl51_142 ),
    inference(avatar_split_clause,[],[f1700,f1693,f3683])).

fof(f1700,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | sK3(sK0) = sK5(sK0,X0) )
    | ~ spl51_142 ),
    inference(resolution,[],[f1694,f163])).

fof(f1694,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0)))
        | ~ r2_hidden(X0,k1_tarski(sK3(sK0))) )
    | ~ spl51_142 ),
    inference(avatar_component_clause,[],[f1693])).

fof(f3359,plain,
    ( spl51_224
    | spl51_226
    | ~ spl51_218 ),
    inference(avatar_split_clause,[],[f3342,f3335,f3357,f3351])).

fof(f3335,plain,
    ( spl51_218
  <=> m1_subset_1(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_218])])).

fof(f3342,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK6(sK0),sK0)
    | ~ spl51_218 ),
    inference(resolution,[],[f3336,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t2_subset)).

fof(f3336,plain,
    ( m1_subset_1(sK6(sK0),sK0)
    | ~ spl51_218 ),
    inference(avatar_component_clause,[],[f3335])).

fof(f3337,plain,
    ( spl51_218
    | ~ spl51_124
    | ~ spl51_206 ),
    inference(avatar_split_clause,[],[f3282,f3253,f1418,f3335])).

fof(f1418,plain,
    ( spl51_124
  <=> r2_hidden(sK6(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_124])])).

fof(f3253,plain,
    ( spl51_206
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_206])])).

fof(f3282,plain,
    ( m1_subset_1(sK6(sK0),sK0)
    | ~ spl51_124
    | ~ spl51_206 ),
    inference(resolution,[],[f3254,f1419])).

fof(f1419,plain,
    ( r2_hidden(sK6(sK0),sK4(sK0))
    | ~ spl51_124 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f3254,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0))
        | m1_subset_1(X0,sK0) )
    | ~ spl51_206 ),
    inference(avatar_component_clause,[],[f3253])).

fof(f3271,plain,
    ( spl51_206
    | ~ spl51_112 ),
    inference(avatar_split_clause,[],[f2837,f1196,f3253])).

fof(f1196,plain,
    ( spl51_112
  <=> m1_subset_1(sK4(sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_112])])).

fof(f2837,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK4(sK0)) )
    | ~ spl51_112 ),
    inference(resolution,[],[f1197,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t4_subset)).

fof(f1197,plain,
    ( m1_subset_1(sK4(sK0),k1_zfmisc_1(sK0))
    | ~ spl51_112 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f2929,plain,
    ( spl51_174
    | ~ spl51_124 ),
    inference(avatar_split_clause,[],[f2369,f1418,f2927])).

fof(f2369,plain,
    ( ! [X0] : r2_hidden(sK6(sK0),k2_xboole_0(sK4(sK0),X0))
    | ~ spl51_124 ),
    inference(resolution,[],[f1419,f165])).

fof(f165,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f155])).

fof(f155,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2538,plain,
    ( spl51_168
    | ~ spl51_0
    | spl51_7
    | spl51_65 ),
    inference(avatar_split_clause,[],[f1687,f672,f282,f261,f2536])).

fof(f672,plain,
    ( spl51_65
  <=> ~ r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_65])])).

fof(f1687,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65 ),
    inference(subsumption_resolution,[],[f798,f673])).

fof(f673,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl51_65 ),
    inference(avatar_component_clause,[],[f672])).

fof(f798,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f784,f283])).

fof(f784,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | r2_hidden(sK5(sK0,X0),k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0 ),
    inference(resolution,[],[f248,f262])).

fof(f248,plain,(
    ! [X0,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X5),k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2472,plain,
    ( spl51_162
    | ~ spl51_0
    | spl51_7
    | spl51_65 ),
    inference(avatar_split_clause,[],[f1625,f672,f282,f261,f2470])).

fof(f1625,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65 ),
    inference(subsumption_resolution,[],[f701,f673])).

fof(f701,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f700,f283])).

fof(f700,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r1_tarski(sK5(sK0,X0),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0))))
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0 ),
    inference(resolution,[],[f249,f262])).

fof(f249,plain,(
    ! [X0,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK5(X0,X5),X5)
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK5(X0,X5),X5)
      | ~ r2_hidden(X5,k2_xboole_0(sK4(X0),k1_tarski(sK3(X0))))
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2450,plain,
    ( spl51_158
    | ~ spl51_0
    | spl51_7
    | spl51_65
    | spl51_123 ),
    inference(avatar_split_clause,[],[f2446,f1409,f672,f282,f261,f2448])).

fof(f2446,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65
    | ~ spl51_123 ),
    inference(subsumption_resolution,[],[f2358,f1410])).

fof(f2358,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | k1_xboole_0 = sK4(sK0) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65 ),
    inference(subsumption_resolution,[],[f670,f673])).

fof(f670,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | k1_xboole_0 = sK4(sK0)
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f669,f283])).

fof(f669,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | r1_tarski(X0,sK6(sK0))
        | ~ r2_hidden(X0,sK4(sK0))
        | k1_xboole_0 = sK4(sK0)
        | r2_hidden(sK2(sK0),sK0) )
    | ~ spl51_0 ),
    inference(resolution,[],[f246,f262])).

fof(f246,plain,(
    ! [X0,X8] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r1_tarski(X8,sK6(X0))
      | ~ r2_hidden(X8,sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X8] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X8,sK6(X0))
      | ~ r2_hidden(X8,sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1695,plain,
    ( spl51_142
    | ~ spl51_0
    | spl51_7
    | spl51_65
    | ~ spl51_122 ),
    inference(avatar_split_clause,[],[f1691,f1412,f672,f282,f261,f1693])).

fof(f1691,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3(sK0)))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65
    | ~ spl51_122 ),
    inference(forward_demodulation,[],[f1690,f322])).

fof(f1690,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(k1_xboole_0,k1_tarski(sK3(sK0))))
        | r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65
    | ~ spl51_122 ),
    inference(forward_demodulation,[],[f1689,f1413])).

fof(f1689,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k1_tarski(sK3(sK0)))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65
    | ~ spl51_122 ),
    inference(forward_demodulation,[],[f1688,f322])).

fof(f1688,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),k2_xboole_0(k1_xboole_0,k1_tarski(sK3(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK4(sK0),k1_tarski(sK3(sK0)))) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65
    | ~ spl51_122 ),
    inference(forward_demodulation,[],[f1687,f1413])).

fof(f1420,plain,
    ( spl51_122
    | spl51_124
    | ~ spl51_0
    | spl51_7
    | spl51_65 ),
    inference(avatar_split_clause,[],[f1403,f672,f282,f261,f1418,f1412])).

fof(f1403,plain,
    ( r2_hidden(sK6(sK0),sK4(sK0))
    | k1_xboole_0 = sK4(sK0)
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65 ),
    inference(subsumption_resolution,[],[f619,f673])).

fof(f619,plain,
    ( r2_hidden(sK6(sK0),sK4(sK0))
    | k1_xboole_0 = sK4(sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f618,f283])).

fof(f618,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK6(sK0),sK4(sK0))
    | k1_xboole_0 = sK4(sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0 ),
    inference(resolution,[],[f245,f262])).

fof(f245,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0),sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0),sK4(X0))
      | k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1251,plain,
    ( spl51_114
    | ~ spl51_0
    | spl51_7
    | spl51_87 ),
    inference(avatar_split_clause,[],[f1247,f808,f282,f261,f1249])).

fof(f808,plain,
    ( spl51_87
  <=> ~ r1_tarski(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_87])])).

fof(f1247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_87 ),
    inference(subsumption_resolution,[],[f569,f809])).

fof(f809,plain,
    ( ~ r1_tarski(sK4(sK0),sK0)
    | ~ spl51_87 ),
    inference(avatar_component_clause,[],[f808])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(sK4(sK0),sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f568,f283])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK0
        | r1_tarski(sK4(sK0),sK0)
        | r1_tarski(X0,sK2(sK0)) )
    | ~ spl51_0 ),
    inference(resolution,[],[f251,f262])).

fof(f251,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r1_tarski(sK4(X0),X0)
      | r1_tarski(X2,sK2(X0)) ) ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,sK2(X0))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | r1_tarski(sK4(X0),X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1198,plain,
    ( spl51_112
    | ~ spl51_86 ),
    inference(avatar_split_clause,[],[f1185,f811,f1196])).

fof(f811,plain,
    ( spl51_86
  <=> r1_tarski(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_86])])).

fof(f1185,plain,
    ( m1_subset_1(sK4(sK0),k1_zfmisc_1(sK0))
    | ~ spl51_86 ),
    inference(resolution,[],[f812,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',t3_subset)).

fof(f812,plain,
    ( r1_tarski(sK4(sK0),sK0)
    | ~ spl51_86 ),
    inference(avatar_component_clause,[],[f811])).

fof(f1180,plain,
    ( ~ spl51_64
    | spl51_109 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | ~ spl51_64
    | ~ spl51_109 ),
    inference(subsumption_resolution,[],[f1177,f676])).

fof(f1177,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl51_109 ),
    inference(resolution,[],[f1167,f82])).

fof(f1167,plain,
    ( ~ r2_hidden(sK1(sK2(sK0)),sK0)
    | ~ spl51_109 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f986,plain,
    ( spl51_94
    | ~ spl51_2 ),
    inference(avatar_split_clause,[],[f479,f268,f984])).

fof(f268,plain,
    ( spl51_2
  <=> v6_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_2])])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0)
        | r3_xboole_0(X1,X0) )
    | ~ spl51_2 ),
    inference(resolution,[],[f129,f269])).

fof(f269,plain,
    ( v6_ordinal1(sK0)
    | ~ spl51_2 ),
    inference(avatar_component_clause,[],[f268])).

fof(f129,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_ordinal1(X0)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X3,X0)
      | r3_xboole_0(X3,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v6_ordinal1(X0)
        | ( ~ r3_xboole_0(sK8(X0),sK9(X0))
          & r2_hidden(sK9(X0),X0)
          & r2_hidden(sK8(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r3_xboole_0(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v6_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f62,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r3_xboole_0(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r3_xboole_0(sK8(X0),sK9(X0))
        & r2_hidden(sK9(X0),X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( v6_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r3_xboole_0(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r3_xboole_0(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v6_ordinal1(X0) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v6_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r3_xboole_0(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r3_xboole_0(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v6_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v6_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r3_xboole_0(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v6_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r3_xboole_0(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v6_ordinal1(X0)
    <=> ! [X1,X2] :
          ( ( r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t31_finset_1.p',d9_ordinal1)).

fof(f813,plain,
    ( spl51_86
    | ~ spl51_0
    | spl51_7
    | spl51_65 ),
    inference(avatar_split_clause,[],[f806,f672,f282,f261,f811])).

fof(f806,plain,
    ( r1_tarski(sK4(sK0),sK0)
    | ~ spl51_0
    | ~ spl51_7
    | ~ spl51_65 ),
    inference(subsumption_resolution,[],[f509,f673])).

fof(f509,plain,
    ( r1_tarski(sK4(sK0),sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f508,f283])).

fof(f508,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK4(sK0),sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0 ),
    inference(resolution,[],[f244,f262])).

fof(f244,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r1_tarski(sK4(X0),X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r1_tarski(sK4(X0),X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f683,plain,
    ( spl51_64
    | spl51_66
    | ~ spl51_0
    | spl51_7 ),
    inference(avatar_split_clause,[],[f503,f282,f261,f681,f675])).

fof(f503,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0
    | ~ spl51_7 ),
    inference(subsumption_resolution,[],[f502,f283])).

fof(f502,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK3(sK0),sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl51_0 ),
    inference(resolution,[],[f243,f262])).

fof(f243,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f284,plain,(
    ~ spl51_7 ),
    inference(avatar_split_clause,[],[f80,f282])).

fof(f80,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f270,plain,(
    spl51_2 ),
    inference(avatar_split_clause,[],[f81,f268])).

fof(f81,plain,(
    v6_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f263,plain,(
    spl51_0 ),
    inference(avatar_split_clause,[],[f79,f261])).

fof(f79,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
