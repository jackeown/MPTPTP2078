%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t82_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 186 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 ( 705 expanded)
%              Number of equality atoms :   52 ( 118 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f181,f345,f1684,f2389,f10419,f10452,f41057,f41070,f41087,f46318,f48068,f48113])).

fof(f48113,plain,
    ( spl4_69
    | ~ spl4_328 ),
    inference(avatar_contradiction_clause,[],[f48112])).

fof(f48112,plain,
    ( $false
    | ~ spl4_69
    | ~ spl4_328 ),
    inference(trivial_inequality_removal,[],[f48098])).

fof(f48098,plain,
    ( k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
    | ~ spl4_69
    | ~ spl4_328 ),
    inference(backward_demodulation,[],[f48070,f1849])).

fof(f1849,plain,
    ( k1_zfmisc_1(sK0) != k1_zfmisc_1(k2_xboole_0(sK0,sK1))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f1848])).

fof(f1848,plain,
    ( spl4_69
  <=> k1_zfmisc_1(sK0) != k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f48070,plain,
    ( k2_xboole_0(sK0,sK1) = sK0
    | ~ spl4_328 ),
    inference(resolution,[],[f48067,f160])).

fof(f160,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',t7_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d10_xboole_0)).

fof(f48067,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl4_328 ),
    inference(avatar_component_clause,[],[f48066])).

fof(f48066,plain,
    ( spl4_328
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_328])])).

fof(f48068,plain,
    ( spl4_328
    | ~ spl4_306 ),
    inference(avatar_split_clause,[],[f48057,f41049,f48066])).

fof(f41049,plain,
    ( spl4_306
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f48057,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl4_306 ),
    inference(resolution,[],[f41050,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d1_zfmisc_1)).

fof(f41050,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_306 ),
    inference(avatar_component_clause,[],[f41049])).

fof(f46318,plain,
    ( spl4_3
    | ~ spl4_312 ),
    inference(avatar_contradiction_clause,[],[f46317])).

fof(f46317,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_312 ),
    inference(subsumption_resolution,[],[f45785,f92])).

fof(f92,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_3
  <=> ~ r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f45785,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl4_312 ),
    inference(superposition,[],[f125,f41086])).

fof(f41086,plain,
    ( k2_xboole_0(sK1,sK0) = sK1
    | ~ spl4_312 ),
    inference(avatar_component_clause,[],[f41085])).

fof(f41085,plain,
    ( spl4_312
  <=> k2_xboole_0(sK1,sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_312])])).

fof(f125,plain,(
    ! [X2,X1] : r3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f117,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f117,plain,(
    ! [X2,X1] : r3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(resolution,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d9_xboole_0)).

fof(f41087,plain,
    ( spl4_312
    | ~ spl4_310 ),
    inference(avatar_split_clause,[],[f41072,f41068,f41085])).

fof(f41068,plain,
    ( spl4_310
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f41072,plain,
    ( k2_xboole_0(sK1,sK0) = sK1
    | ~ spl4_310 ),
    inference(resolution,[],[f41069,f297])).

fof(f297,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X2),X2)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f160,f52])).

fof(f41069,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl4_310 ),
    inference(avatar_component_clause,[],[f41068])).

fof(f41070,plain,
    ( spl4_310
    | ~ spl4_308 ),
    inference(avatar_split_clause,[],[f41058,f41055,f41068])).

fof(f41055,plain,
    ( spl4_308
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_308])])).

fof(f41058,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl4_308 ),
    inference(resolution,[],[f41056,f76])).

fof(f41056,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_308 ),
    inference(avatar_component_clause,[],[f41055])).

fof(f41057,plain,
    ( spl4_306
    | spl4_308
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f1687,f1682,f41055,f41049])).

fof(f1682,plain,
    ( spl4_58
  <=> ! [X0] :
        ( r2_hidden(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | ~ r1_tarski(X0,k2_xboole_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1687,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_58 ),
    inference(resolution,[],[f1683,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1683,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | r2_hidden(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f1682])).

fof(f10452,plain,
    ( spl4_3
    | ~ spl4_140 ),
    inference(avatar_contradiction_clause,[],[f10451])).

fof(f10451,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_140 ),
    inference(subsumption_resolution,[],[f10448,f92])).

fof(f10448,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl4_140 ),
    inference(resolution,[],[f10418,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10418,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f10417])).

fof(f10417,plain,
    ( spl4_140
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f10419,plain,
    ( spl4_140
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f9948,f2387,f10417])).

fof(f2387,plain,
    ( spl4_80
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f9948,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f2388,f76])).

fof(f2388,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2389,plain,
    ( spl4_80
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f2274,f1851,f2387])).

fof(f1851,plain,
    ( spl4_68
  <=> k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f2274,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_68 ),
    inference(superposition,[],[f1538,f1852])).

fof(f1852,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1538,plain,(
    ! [X0,X1] : r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f285,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',idempotence_k2_xboole_0)).

fof(f285,plain,(
    ! [X6,X7,X5] : r2_hidden(X5,k2_xboole_0(X6,k1_zfmisc_1(k2_xboole_0(X7,X5)))) ),
    inference(resolution,[],[f151,f126])).

fof(f126,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f51,f52])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(X0,k2_xboole_0(X1,k1_zfmisc_1(X2))) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d3_xboole_0)).

fof(f1684,plain,
    ( spl4_58
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f346,f343,f1682])).

fof(f343,plain,
    ( spl4_22
  <=> ! [X10] :
        ( ~ r2_hidden(X10,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
        | r2_hidden(X10,k1_zfmisc_1(sK0))
        | r2_hidden(X10,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f346,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | ~ r1_tarski(X0,k2_xboole_0(sK0,sK1)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f344,f75])).

fof(f344,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
        | r2_hidden(X10,k1_zfmisc_1(sK0))
        | r2_hidden(X10,k1_zfmisc_1(sK1)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f343])).

fof(f345,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f194,f179,f343])).

fof(f179,plain,
    ( spl4_18
  <=> k1_zfmisc_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f194,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
        | r2_hidden(X10,k1_zfmisc_1(sK0))
        | r2_hidden(X10,k1_zfmisc_1(sK1)) )
    | ~ spl4_18 ),
    inference(superposition,[],[f79,f180])).

fof(f180,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f181,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f44,f179])).

fof(f44,plain,(
    k1_zfmisc_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k1_zfmisc_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k1_zfmisc_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',t82_zfmisc_1)).

fof(f93,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
