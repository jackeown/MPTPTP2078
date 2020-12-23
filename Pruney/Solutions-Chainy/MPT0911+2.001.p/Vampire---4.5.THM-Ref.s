%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:28 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 548 expanded)
%              Number of leaves         :   17 ( 147 expanded)
%              Depth                    :   21
%              Number of atoms          :  398 (3341 expanded)
%              Number of equality atoms :  231 (2043 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f444,f644,f763])).

fof(f763,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f710,f352])).

fof(f352,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f351,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).

% (21685)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (21684)Refutation not found, incomplete strategy% (21684)------------------------------
% (21684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21669)Termination reason: Refutation not found, incomplete strategy

% (21669)Memory used [KB]: 1663
% (21669)Time elapsed: 0.145 s
% (21669)------------------------------
% (21669)------------------------------
% (21692)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (21692)Refutation not found, incomplete strategy% (21692)------------------------------
% (21692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f351,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f350,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f350,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f349,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f349,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f319,f210])).

fof(f210,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f198,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_2 ),
    inference(superposition,[],[f91,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl9_2 ),
    inference(resolution,[],[f109,f98])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
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

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f109,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f66,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f198,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4) ),
    inference(superposition,[],[f92,f91])).

fof(f92,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f319,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(superposition,[],[f88,f111])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f710,plain,
    ( k1_xboole_0 != sK3
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f583,f352])).

fof(f583,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f47,f572])).

fof(f572,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f571,f44])).

fof(f571,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f570,f45])).

fof(f570,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f564,f46])).

fof(f564,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f80,f78])).

fof(f78,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

% (21684)Termination reason: Refutation not found, incomplete strategy

% (21684)Memory used [KB]: 10618
% (21684)Time elapsed: 0.161 s
% (21684)------------------------------
% (21684)------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f47,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f644,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f642,f474])).

fof(f474,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f468,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f468,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f461,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f461,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_1 ),
    inference(resolution,[],[f105,f60])).

fof(f105,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f642,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f641,f471])).

fof(f471,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f467,f54])).

fof(f467,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f461,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f641,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f640,f464])).

fof(f464,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f460,f54])).

fof(f460,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f105,f61])).

fof(f640,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(subsumption_resolution,[],[f639,f583])).

fof(f639,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(trivial_inequality_removal,[],[f637])).

fof(f637,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(superposition,[],[f77,f632])).

fof(f632,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f631,f610])).

fof(f610,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f609,f44])).

fof(f609,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f608,f45])).

fof(f608,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f602,f46])).

fof(f602,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f82,f78])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f631,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f630,f594])).

fof(f594,plain,(
    k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f593,f44])).

fof(f593,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f592,f45])).

fof(f592,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f586,f46])).

fof(f586,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f81,f78])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f630,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f629,f572])).

fof(f629,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f628,f44])).

fof(f628,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f627,f45])).

fof(f627,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f621,f46])).

fof(f621,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f79,f78])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f77,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f43,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f444,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f443,f107,f103])).

fof(f443,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f78,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21691)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (21683)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (21675)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (21670)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (21673)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (21677)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (21668)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (21688)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (21681)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (21674)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (21694)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (21680)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (21671)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (21680)Refutation not found, incomplete strategy% (21680)------------------------------
% 0.22/0.54  % (21680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21680)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21680)Memory used [KB]: 10618
% 0.22/0.54  % (21680)Time elapsed: 0.133 s
% 0.22/0.54  % (21680)------------------------------
% 0.22/0.54  % (21680)------------------------------
% 0.22/0.54  % (21672)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (21696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (21676)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (21697)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (21697)Refutation not found, incomplete strategy% (21697)------------------------------
% 0.22/0.54  % (21697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21697)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21697)Memory used [KB]: 1663
% 0.22/0.54  % (21697)Time elapsed: 0.001 s
% 0.22/0.54  % (21697)------------------------------
% 0.22/0.54  % (21697)------------------------------
% 0.22/0.55  % (21689)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (21686)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (21695)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (21682)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (21690)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (21686)Refutation not found, incomplete strategy% (21686)------------------------------
% 0.22/0.55  % (21686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21686)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21686)Memory used [KB]: 1791
% 0.22/0.55  % (21686)Time elapsed: 0.141 s
% 0.22/0.55  % (21686)------------------------------
% 0.22/0.55  % (21686)------------------------------
% 0.22/0.55  % (21695)Refutation not found, incomplete strategy% (21695)------------------------------
% 0.22/0.55  % (21695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21695)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21695)Memory used [KB]: 6268
% 0.22/0.55  % (21695)Time elapsed: 0.139 s
% 0.22/0.55  % (21695)------------------------------
% 0.22/0.55  % (21695)------------------------------
% 0.22/0.55  % (21687)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (21678)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.56  % (21679)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.56  % (21669)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.56  % (21669)Refutation not found, incomplete strategy% (21669)------------------------------
% 1.44/0.56  % (21669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21682)Refutation not found, incomplete strategy% (21682)------------------------------
% 1.44/0.56  % (21682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21682)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21682)Memory used [KB]: 1791
% 1.44/0.56  % (21682)Time elapsed: 0.134 s
% 1.44/0.56  % (21682)------------------------------
% 1.44/0.56  % (21682)------------------------------
% 1.44/0.56  % (21693)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (21694)Refutation not found, incomplete strategy% (21694)------------------------------
% 1.44/0.56  % (21694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21694)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21694)Memory used [KB]: 6268
% 1.44/0.56  % (21694)Time elapsed: 0.131 s
% 1.44/0.56  % (21694)------------------------------
% 1.44/0.56  % (21694)------------------------------
% 1.44/0.56  % (21684)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.56  % (21674)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f775,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f444,f644,f763])).
% 1.44/0.56  fof(f763,plain,(
% 1.44/0.56    ~spl9_2),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f762])).
% 1.44/0.56  fof(f762,plain,(
% 1.44/0.56    $false | ~spl9_2),
% 1.44/0.56    inference(subsumption_resolution,[],[f710,f352])).
% 1.44/0.56  fof(f352,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl9_2),
% 1.44/0.56    inference(subsumption_resolution,[],[f351,f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    k1_xboole_0 != sK0),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).
% 1.44/0.56  % (21685)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.56  % (21684)Refutation not found, incomplete strategy% (21684)------------------------------
% 1.44/0.56  % (21684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21669)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21669)Memory used [KB]: 1663
% 1.44/0.56  % (21669)Time elapsed: 0.145 s
% 1.44/0.56  % (21669)------------------------------
% 1.44/0.56  % (21669)------------------------------
% 1.44/0.57  % (21692)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.64/0.58  % (21692)Refutation not found, incomplete strategy% (21692)------------------------------
% 1.64/0.58  % (21692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.64/0.58    inference(flattening,[],[f17])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.64/0.58    inference(ennf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    inference(negated_conjecture,[],[f15])).
% 1.64/0.58  fof(f15,conjecture,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.64/0.58  fof(f351,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 1.64/0.58    inference(subsumption_resolution,[],[f350,f45])).
% 1.64/0.58  fof(f45,plain,(
% 1.64/0.58    k1_xboole_0 != sK1),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f350,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 1.64/0.58    inference(subsumption_resolution,[],[f349,f46])).
% 1.64/0.58  fof(f46,plain,(
% 1.64/0.58    k1_xboole_0 != sK2),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f349,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 1.64/0.58    inference(subsumption_resolution,[],[f319,f210])).
% 1.64/0.58  fof(f210,plain,(
% 1.64/0.58    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) ) | ~spl9_2),
% 1.64/0.58    inference(forward_demodulation,[],[f198,f185])).
% 1.64/0.58  fof(f185,plain,(
% 1.64/0.58    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl9_2),
% 1.64/0.58    inference(superposition,[],[f91,f111])).
% 1.64/0.58  fof(f111,plain,(
% 1.64/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl9_2),
% 1.64/0.58    inference(resolution,[],[f109,f98])).
% 1.64/0.58  fof(f98,plain,(
% 1.64/0.58    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.64/0.58    inference(resolution,[],[f50,f48])).
% 1.64/0.58  fof(f48,plain,(
% 1.64/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(rectify,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.58    inference(nnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.58  fof(f50,plain,(
% 1.64/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.64/0.58  fof(f109,plain,(
% 1.64/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_2),
% 1.64/0.58    inference(avatar_component_clause,[],[f107])).
% 1.64/0.58  fof(f107,plain,(
% 1.64/0.58    spl9_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.64/0.58  fof(f91,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.64/0.58    inference(equality_resolution,[],[f84])).
% 1.64/0.58  fof(f84,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f72,f76])).
% 1.64/0.58  fof(f76,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f66,f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.64/0.58  fof(f72,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f39])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.58    inference(flattening,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.58    inference(nnf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.64/0.58  fof(f198,plain,(
% 1.64/0.58    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4)) )),
% 1.64/0.58    inference(superposition,[],[f92,f91])).
% 1.64/0.58  fof(f92,plain,(
% 1.64/0.58    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.64/0.58    inference(equality_resolution,[],[f85])).
% 1.64/0.58  fof(f85,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f71,f76])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f39])).
% 1.64/0.58  fof(f319,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 1.64/0.58    inference(superposition,[],[f88,f111])).
% 1.64/0.58  fof(f88,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f68,f76])).
% 1.64/0.58  fof(f68,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f39])).
% 1.64/0.58  fof(f710,plain,(
% 1.64/0.58    k1_xboole_0 != sK3 | ~spl9_2),
% 1.64/0.58    inference(backward_demodulation,[],[f583,f352])).
% 1.64/0.58  fof(f583,plain,(
% 1.64/0.58    sK3 != k2_mcart_1(sK4)),
% 1.64/0.58    inference(superposition,[],[f47,f572])).
% 1.64/0.58  fof(f572,plain,(
% 1.64/0.58    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 1.64/0.58    inference(subsumption_resolution,[],[f571,f44])).
% 1.64/0.58  fof(f571,plain,(
% 1.64/0.58    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 1.64/0.58    inference(subsumption_resolution,[],[f570,f45])).
% 1.64/0.58  fof(f570,plain,(
% 1.64/0.58    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.58    inference(subsumption_resolution,[],[f564,f46])).
% 1.64/0.58  fof(f564,plain,(
% 1.64/0.58    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.58    inference(resolution,[],[f80,f78])).
% 1.64/0.58  fof(f78,plain,(
% 1.64/0.58    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.64/0.58    inference(definition_unfolding,[],[f42,f59])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f80,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f65,f59])).
% 1.64/0.58  fof(f65,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.64/0.58    inference(ennf_transformation,[],[f13])).
% 1.64/0.58  % (21684)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (21684)Memory used [KB]: 10618
% 1.64/0.58  % (21684)Time elapsed: 0.161 s
% 1.64/0.58  % (21684)------------------------------
% 1.64/0.58  % (21684)------------------------------
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f644,plain,(
% 1.64/0.58    ~spl9_1),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f643])).
% 1.64/0.58  fof(f643,plain,(
% 1.64/0.58    $false | ~spl9_1),
% 1.64/0.58    inference(subsumption_resolution,[],[f642,f474])).
% 1.64/0.58  fof(f474,plain,(
% 1.64/0.58    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 1.64/0.58    inference(resolution,[],[f468,f54])).
% 1.64/0.58  fof(f54,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.64/0.58  fof(f468,plain,(
% 1.64/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 1.64/0.58    inference(resolution,[],[f461,f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.64/0.58    inference(ennf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.64/0.58  fof(f461,plain,(
% 1.64/0.58    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl9_1),
% 1.64/0.58    inference(resolution,[],[f105,f60])).
% 1.64/0.59  fof(f105,plain,(
% 1.64/0.59    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_1),
% 1.64/0.59    inference(avatar_component_clause,[],[f103])).
% 1.64/0.59  fof(f103,plain,(
% 1.64/0.59    spl9_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.64/0.59  fof(f642,plain,(
% 1.64/0.59    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 1.64/0.59    inference(subsumption_resolution,[],[f641,f471])).
% 1.64/0.59  fof(f471,plain,(
% 1.64/0.59    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl9_1),
% 1.64/0.59    inference(resolution,[],[f467,f54])).
% 1.64/0.59  fof(f467,plain,(
% 1.64/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl9_1),
% 1.64/0.59    inference(resolution,[],[f461,f61])).
% 1.64/0.59  fof(f61,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f23])).
% 1.64/0.59  fof(f641,plain,(
% 1.64/0.59    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 1.64/0.59    inference(subsumption_resolution,[],[f640,f464])).
% 1.64/0.59  fof(f464,plain,(
% 1.64/0.59    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl9_1),
% 1.64/0.59    inference(resolution,[],[f460,f54])).
% 1.64/0.59  fof(f460,plain,(
% 1.64/0.59    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl9_1),
% 1.64/0.59    inference(resolution,[],[f105,f61])).
% 1.64/0.59  fof(f640,plain,(
% 1.64/0.59    ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.64/0.59    inference(subsumption_resolution,[],[f639,f583])).
% 1.64/0.59  fof(f639,plain,(
% 1.64/0.59    sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.64/0.59    inference(trivial_inequality_removal,[],[f637])).
% 1.64/0.59  fof(f637,plain,(
% 1.64/0.59    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.64/0.59    inference(superposition,[],[f77,f632])).
% 1.64/0.59  fof(f632,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))),
% 1.64/0.59    inference(forward_demodulation,[],[f631,f610])).
% 1.64/0.59  fof(f610,plain,(
% 1.64/0.59    k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.64/0.59    inference(subsumption_resolution,[],[f609,f44])).
% 1.64/0.59  fof(f609,plain,(
% 1.64/0.59    k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f608,f45])).
% 1.64/0.59  fof(f608,plain,(
% 1.64/0.59    k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f602,f46])).
% 1.64/0.59  fof(f602,plain,(
% 1.64/0.59    k1_mcart_1(k1_mcart_1(sK4)) = k5_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(resolution,[],[f82,f78])).
% 1.64/0.59  fof(f82,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(definition_unfolding,[],[f63,f59])).
% 1.64/0.59  fof(f63,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f631,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))),
% 1.64/0.59    inference(forward_demodulation,[],[f630,f594])).
% 1.64/0.59  fof(f594,plain,(
% 1.64/0.59    k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 1.64/0.59    inference(subsumption_resolution,[],[f593,f44])).
% 1.64/0.59  fof(f593,plain,(
% 1.64/0.59    k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f592,f45])).
% 1.64/0.59  fof(f592,plain,(
% 1.64/0.59    k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f586,f46])).
% 1.64/0.59  fof(f586,plain,(
% 1.64/0.59    k2_mcart_1(k1_mcart_1(sK4)) = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(resolution,[],[f81,f78])).
% 1.64/0.59  fof(f81,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(definition_unfolding,[],[f64,f59])).
% 1.64/0.59  fof(f64,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f630,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k2_mcart_1(sK4))),
% 1.64/0.59    inference(forward_demodulation,[],[f629,f572])).
% 1.64/0.59  fof(f629,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 1.64/0.59    inference(subsumption_resolution,[],[f628,f44])).
% 1.64/0.59  fof(f628,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f627,f45])).
% 1.64/0.59  fof(f627,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(subsumption_resolution,[],[f621,f46])).
% 1.64/0.59  fof(f621,plain,(
% 1.64/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.59    inference(resolution,[],[f79,f78])).
% 1.64/0.59  fof(f79,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(definition_unfolding,[],[f62,f58,f59])).
% 1.64/0.59  fof(f58,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f6])).
% 1.64/0.59  fof(f6,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.64/0.59  fof(f62,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.64/0.59    inference(ennf_transformation,[],[f12])).
% 1.64/0.59  fof(f12,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.64/0.59  fof(f77,plain,(
% 1.64/0.59    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.64/0.59    inference(definition_unfolding,[],[f43,f58])).
% 1.64/0.59  fof(f43,plain,(
% 1.64/0.59    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f444,plain,(
% 1.64/0.59    spl9_1 | spl9_2),
% 1.64/0.59    inference(avatar_split_clause,[],[f443,f107,f103])).
% 1.64/0.59  fof(f443,plain,(
% 1.64/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.64/0.59    inference(resolution,[],[f78,f53])).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.64/0.59    inference(flattening,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.64/0.59    inference(ennf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (21674)------------------------------
% 1.64/0.59  % (21674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (21674)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (21674)Memory used [KB]: 11001
% 1.64/0.59  % (21674)Time elapsed: 0.143 s
% 1.64/0.59  % (21674)------------------------------
% 1.64/0.59  % (21674)------------------------------
% 1.64/0.59  % (21667)Success in time 0.219 s
%------------------------------------------------------------------------------
