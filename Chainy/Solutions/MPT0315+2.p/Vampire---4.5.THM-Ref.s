%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0315+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 206 expanded)
%              Number of leaves         :   14 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 487 expanded)
%              Number of equality atoms :   47 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1168,f1610,f2104])).

fof(f2104,plain,(
    ~ spl24_1 ),
    inference(avatar_contradiction_clause,[],[f2103])).

fof(f2103,plain,
    ( $false
    | ~ spl24_1 ),
    inference(subsumption_resolution,[],[f2100,f1754])).

fof(f1754,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl24_1 ),
    inference(resolution,[],[f1713,f729])).

fof(f729,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f578])).

fof(f578,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f474,f577])).

fof(f577,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f474,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1713,plain,
    ( ! [X29] : ~ r2_hidden(X29,k1_xboole_0)
    | ~ spl24_1 ),
    inference(forward_demodulation,[],[f1712,f1711])).

fof(f1711,plain,
    ( k1_xboole_0 = k4_xboole_0(sK5,sK5)
    | ~ spl24_1 ),
    inference(forward_demodulation,[],[f1705,f1698])).

fof(f1698,plain,
    ( sK5 = k4_xboole_0(sK5,sK6)
    | ~ spl24_1 ),
    inference(resolution,[],[f1164,f719])).

fof(f719,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f575])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1164,plain,
    ( r1_xboole_0(sK5,sK6)
    | ~ spl24_1 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl24_1
  <=> r1_xboole_0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_1])])).

fof(f1705,plain,
    ( k1_xboole_0 = k4_xboole_0(sK5,k4_xboole_0(sK5,sK6))
    | ~ spl24_1 ),
    inference(resolution,[],[f1164,f990])).

fof(f990,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f721,f782])).

fof(f782,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f721,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f576])).

fof(f576,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1712,plain,
    ( ! [X29] : ~ r2_hidden(X29,k4_xboole_0(sK5,sK5))
    | ~ spl24_1 ),
    inference(forward_demodulation,[],[f1706,f1698])).

fof(f1706,plain,
    ( ! [X29] : ~ r2_hidden(X29,k4_xboole_0(sK5,k4_xboole_0(sK5,sK6)))
    | ~ spl24_1 ),
    inference(resolution,[],[f1164,f995])).

fof(f995,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f733,f782])).

fof(f733,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f580])).

fof(f580,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f475,f579])).

fof(f579,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f475,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f421])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2100,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK6,sK8))
    | ~ spl24_1 ),
    inference(backward_demodulation,[],[f1215,f2098])).

fof(f2098,plain,
    ( ! [X28,X27] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK5,X27),k4_xboole_0(k2_zfmisc_1(sK5,X27),k2_zfmisc_1(sK6,X28)))
    | ~ spl24_1 ),
    inference(forward_demodulation,[],[f2097,f1127])).

fof(f1127,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f682])).

fof(f682,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f574])).

fof(f574,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f573])).

fof(f573,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f323])).

fof(f323,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2097,plain,
    ( ! [X28,X27] : k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X27,k4_xboole_0(X27,X28))) = k4_xboole_0(k2_zfmisc_1(sK5,X27),k4_xboole_0(k2_zfmisc_1(sK5,X27),k2_zfmisc_1(sK6,X28)))
    | ~ spl24_1 ),
    inference(forward_demodulation,[],[f2042,f1711])).

fof(f2042,plain,
    ( ! [X28,X27] : k4_xboole_0(k2_zfmisc_1(sK5,X27),k4_xboole_0(k2_zfmisc_1(sK5,X27),k2_zfmisc_1(sK6,X28))) = k2_zfmisc_1(k4_xboole_0(sK5,sK5),k4_xboole_0(X27,k4_xboole_0(X27,X28)))
    | ~ spl24_1 ),
    inference(superposition,[],[f978,f1698])).

fof(f978,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f670,f782,f782,f782])).

fof(f670,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f333])).

fof(f333,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f1215,plain,(
    ~ r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK5,sK7),k4_xboole_0(k2_zfmisc_1(sK5,sK7),k2_zfmisc_1(sK6,sK8))),k2_zfmisc_1(sK6,sK8)) ),
    inference(resolution,[],[f665,f988])).

fof(f988,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f718,f782])).

fof(f718,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f468])).

fof(f468,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f143])).

fof(f143,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f665,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK5,sK7),k2_zfmisc_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f572])).

fof(f572,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK5,sK7),k2_zfmisc_1(sK6,sK8))
    & ( r1_xboole_0(sK7,sK8)
      | r1_xboole_0(sK5,sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f424,f571])).

fof(f571,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK5,sK7),k2_zfmisc_1(sK6,sK8))
      & ( r1_xboole_0(sK7,sK8)
        | r1_xboole_0(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f424,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f338])).

fof(f338,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f337])).

fof(f337,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1610,plain,(
    ~ spl24_2 ),
    inference(avatar_contradiction_clause,[],[f1609])).

fof(f1609,plain,
    ( $false
    | ~ spl24_2 ),
    inference(subsumption_resolution,[],[f1606,f1258])).

fof(f1258,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl24_2 ),
    inference(resolution,[],[f1203,f729])).

fof(f1203,plain,
    ( ! [X29] : ~ r2_hidden(X29,k1_xboole_0)
    | ~ spl24_2 ),
    inference(forward_demodulation,[],[f1202,f1201])).

fof(f1201,plain,
    ( k1_xboole_0 = k4_xboole_0(sK7,sK7)
    | ~ spl24_2 ),
    inference(forward_demodulation,[],[f1195,f1188])).

fof(f1188,plain,
    ( sK7 = k4_xboole_0(sK7,sK8)
    | ~ spl24_2 ),
    inference(resolution,[],[f1167,f719])).

fof(f1167,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ spl24_2 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1166,plain,
    ( spl24_2
  <=> r1_xboole_0(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_2])])).

fof(f1195,plain,
    ( k1_xboole_0 = k4_xboole_0(sK7,k4_xboole_0(sK7,sK8))
    | ~ spl24_2 ),
    inference(resolution,[],[f1167,f990])).

fof(f1202,plain,
    ( ! [X29] : ~ r2_hidden(X29,k4_xboole_0(sK7,sK7))
    | ~ spl24_2 ),
    inference(forward_demodulation,[],[f1196,f1188])).

fof(f1196,plain,
    ( ! [X29] : ~ r2_hidden(X29,k4_xboole_0(sK7,k4_xboole_0(sK7,sK8)))
    | ~ spl24_2 ),
    inference(resolution,[],[f1167,f995])).

fof(f1606,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK6,sK8))
    | ~ spl24_2 ),
    inference(backward_demodulation,[],[f1215,f1604])).

fof(f1604,plain,
    ( ! [X30,X29] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X29,sK7),k4_xboole_0(k2_zfmisc_1(X29,sK7),k2_zfmisc_1(X30,sK8)))
    | ~ spl24_2 ),
    inference(forward_demodulation,[],[f1603,f1126])).

fof(f1126,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f683])).

fof(f683,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f574])).

fof(f1603,plain,
    ( ! [X30,X29] : k4_xboole_0(k2_zfmisc_1(X29,sK7),k4_xboole_0(k2_zfmisc_1(X29,sK7),k2_zfmisc_1(X30,sK8))) = k2_zfmisc_1(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k1_xboole_0)
    | ~ spl24_2 ),
    inference(forward_demodulation,[],[f1547,f1201])).

fof(f1547,plain,
    ( ! [X30,X29] : k4_xboole_0(k2_zfmisc_1(X29,sK7),k4_xboole_0(k2_zfmisc_1(X29,sK7),k2_zfmisc_1(X30,sK8))) = k2_zfmisc_1(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(sK7,sK7))
    | ~ spl24_2 ),
    inference(superposition,[],[f978,f1188])).

fof(f1168,plain,
    ( spl24_1
    | spl24_2 ),
    inference(avatar_split_clause,[],[f664,f1166,f1163])).

fof(f664,plain,
    ( r1_xboole_0(sK7,sK8)
    | r1_xboole_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f572])).
%------------------------------------------------------------------------------
