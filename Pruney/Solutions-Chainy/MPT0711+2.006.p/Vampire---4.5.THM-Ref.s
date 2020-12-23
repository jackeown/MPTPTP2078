%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 (2366 expanded)
%              Number of leaves         :   27 ( 682 expanded)
%              Depth                    :   30
%              Number of atoms          :  677 (8686 expanded)
%              Number of equality atoms :  169 (3384 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f559,f868,f883,f1579,f3163,f3387,f3393])).

fof(f3393,plain,
    ( ~ spl5_6
    | spl5_68 ),
    inference(avatar_split_clause,[],[f3389,f3385,f90])).

fof(f90,plain,
    ( spl5_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3385,plain,
    ( spl5_68
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f3389,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_68 ),
    inference(resolution,[],[f3386,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f3386,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | spl5_68 ),
    inference(avatar_component_clause,[],[f3385])).

fof(f3387,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_3
    | spl5_1
    | ~ spl5_68
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f3382,f3160,f1577,f90,f82,f74,f3385,f70,f78,f82,f86,f90])).

fof(f86,plain,
    ( spl5_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f78,plain,
    ( spl5_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( spl5_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,
    ( spl5_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f82,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1577,plain,
    ( spl5_60
  <=> ! [X37] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f3160,plain,
    ( spl5_65
  <=> k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f3382,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60
    | ~ spl5_65 ),
    inference(duplicate_literal_removal,[],[f3381])).

fof(f3381,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f3380,f75])).

fof(f75,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f3380,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f3379,f1811])).

fof(f1811,plain,
    ( ! [X24] : k7_relat_1(sK0,X24) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X24)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f1788,f1670])).

fof(f1670,plain,
    ( ! [X33] : k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,X33))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f1590,f1578])).

fof(f1578,plain,
    ( ! [X37] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f1590,plain,
    ( ! [X33] :
        ( k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,X33))
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1589,f1462])).

fof(f1462,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f179,f1413])).

fof(f1413,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1410,f75])).

fof(f1410,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))
    | ~ spl5_4 ),
    inference(resolution,[],[f247,f83])).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f247,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(X2)))) = k7_relat_1(X2,X3) ) ),
    inference(forward_demodulation,[],[f245,f94])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_subsumption,[],[f49,f48,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f49,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f245,plain,(
    ! [X2,X3] :
      ( k7_relat_1(X2,k1_relat_1(k6_relat_1(X3))) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(X2))))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f179,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f141,f48])).

fof(f141,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f131,f75])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl5_4 ),
    inference(resolution,[],[f56,f83])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1589,plain,
    ( ! [X33] :
        ( k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33))
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1588,f179])).

fof(f1588,plain,
    ( ! [X33] :
        ( k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))))
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1587,f1462])).

fof(f1587,plain,
    ( ! [X33] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33)))
        | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1586,f1462])).

fof(f1586,plain,
    ( ! [X33] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0))))
        | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1585,f179])).

fof(f1585,plain,
    ( ! [X33] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0))))))
        | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33)) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1440,f1462])).

fof(f1440,plain,
    ( ! [X33] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))))
        | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33)) )
    | ~ spl5_6 ),
    inference(superposition,[],[f1222,f1411])).

fof(f1411,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK0))))
    | ~ spl5_6 ),
    inference(resolution,[],[f247,f91])).

fof(f91,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1222,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
        | k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) )
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1207,f94])).

fof(f1207,plain,
    ( ! [X0] :
        ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK0,X0))))
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) )
    | ~ spl5_6 ),
    inference(superposition,[],[f1010,f107])).

fof(f107,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f105,f94])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X2)),X3)
      | k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X3) ) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f1010,plain,
    ( ! [X9] : k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK0,X9))),k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK0)))))
    | ~ spl5_6 ),
    inference(resolution,[],[f135,f502])).

fof(f502,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))),k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f331,f48])).

fof(f331,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(k6_relat_1(X7))
        | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(sK0))),k1_relat_1(k7_relat_1(sK0,X7))) )
    | ~ spl5_6 ),
    inference(superposition,[],[f54,f260])).

fof(f260,plain,
    ( ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f250,f94])).

fof(f250,plain,
    ( ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0)))))
    | ~ spl5_6 ),
    inference(resolution,[],[f244,f48])).

fof(f244,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,k1_relat_1(sK0)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(sK0,k1_relat_1(X1)))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f50,f91])).

fof(f135,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = X2 ) ),
    inference(forward_demodulation,[],[f133,f94])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(k6_relat_1(X3)))
      | k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = X2 ) ),
    inference(resolution,[],[f56,f48])).

fof(f1788,plain,
    ( ! [X24] : k7_relat_1(sK0,X24) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X24)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f1411,f1462])).

fof(f3379,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f3371,f1812])).

fof(f1812,plain,
    ( ! [X25] : k7_relat_1(sK1,X25) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X25)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f1789,f1670])).

fof(f1789,plain,
    ( ! [X25] : k7_relat_1(sK1,X25) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X25)))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f1413,f1462])).

fof(f3371,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_65 ),
    inference(trivial_inequality_removal,[],[f3370])).

fof(f3370,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_65 ),
    inference(superposition,[],[f53,f3161])).

fof(f3161,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f3160])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
                    & r2_hidden(sK3(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f3163,plain,
    ( spl5_65
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_51
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3119,f1577,f881,f90,f82,f74,f70,f3160])).

fof(f881,plain,
    ( spl5_51
  <=> ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f3119,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_51
    | ~ spl5_60 ),
    inference(resolution,[],[f3089,f46])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f3089,plain,
    ( ! [X9] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9)
        | k7_relat_1(sK0,X9) = k7_relat_1(sK1,X9) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_51
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f3088,f1811])).

fof(f3088,plain,
    ( ! [X9] :
        ( k7_relat_1(sK1,X9) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X9)))
        | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_51
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f3053,f1812])).

fof(f3053,plain,
    ( ! [X9] :
        ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X9))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X9)))
        | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_51
    | ~ spl5_60 ),
    inference(resolution,[],[f882,f1813])).

fof(f1813,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(X29,k1_relat_1(k7_relat_1(sK0,X28)))
        | r2_hidden(X29,X28) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f1792,f1670])).

fof(f1792,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(X29,k1_relat_1(k7_relat_1(sK1,X28)))
        | r2_hidden(X29,X28) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f193,f1462])).

fof(f193,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))
      | r2_hidden(X4,X5) ) ),
    inference(forward_demodulation,[],[f191,f94])).

fof(f191,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))
      | r2_hidden(X4,k1_relat_1(k6_relat_1(X5))) ) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f882,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) )
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1579,plain,
    ( ~ spl5_6
    | spl5_60
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1575,f90,f82,f74,f1577,f90])).

fof(f1575,plain,
    ( ! [X37] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1443,f1462])).

fof(f1443,plain,
    ( ! [X37] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(k6_relat_1(X37),k1_relat_1(sK0))))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f54,f1411])).

fof(f883,plain,
    ( ~ spl5_6
    | spl5_51
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f873,f866,f881,f90])).

fof(f866,plain,
    ( spl5_50
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f873,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_50 ),
    inference(resolution,[],[f867,f55])).

fof(f867,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f866])).

fof(f868,plain,
    ( spl5_50
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f864,f557,f86,f90,f866])).

fof(f557,plain,
    ( spl5_39
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(X0,sK1,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f864,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | r2_hidden(sK3(sK0,sK1,X1),X1) )
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(duplicate_literal_removal,[],[f862])).

fof(f862,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X1),X1) )
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(resolution,[],[f558,f87])).

fof(f87,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f558,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(X0,sK1,X1),X1) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f557])).

fof(f559,plain,
    ( ~ spl5_4
    | spl5_39
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f555,f78,f74,f557,f82])).

fof(f555,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(X0,sK1,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f552,f75])).

fof(f552,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,sK1,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK1))
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f52,f79])).

fof(f79,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f45,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f47,f70])).

fof(f47,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (10838)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10833)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (10846)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (10841)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (10844)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (10847)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (10834)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (10832)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (10851)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (10852)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (10839)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (10848)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (10845)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (10836)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (10835)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (10850)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (10849)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (10837)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (10842)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (10840)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (10843)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.59  % (10838)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f3394,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f559,f868,f883,f1579,f3163,f3387,f3393])).
% 0.21/0.59  fof(f3393,plain,(
% 0.21/0.59    ~spl5_6 | spl5_68),
% 0.21/0.59    inference(avatar_split_clause,[],[f3389,f3385,f90])).
% 0.21/0.59  fof(f90,plain,(
% 0.21/0.59    spl5_6 <=> v1_relat_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.59  fof(f3385,plain,(
% 0.21/0.59    spl5_68 <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.59  fof(f3389,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | spl5_68),
% 0.21/0.59    inference(resolution,[],[f3386,f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.21/0.59  fof(f3386,plain,(
% 0.21/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | spl5_68),
% 0.21/0.59    inference(avatar_component_clause,[],[f3385])).
% 0.21/0.59  fof(f3387,plain,(
% 0.21/0.59    ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_3 | spl5_1 | ~spl5_68 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60 | ~spl5_65),
% 0.21/0.59    inference(avatar_split_clause,[],[f3382,f3160,f1577,f90,f82,f74,f3385,f70,f78,f82,f86,f90])).
% 0.21/0.59  fof(f86,plain,(
% 0.21/0.59    spl5_5 <=> v1_funct_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    spl5_3 <=> v1_funct_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    spl5_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.59  fof(f74,plain,(
% 0.21/0.59    spl5_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    spl5_4 <=> v1_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.59  fof(f1577,plain,(
% 0.21/0.59    spl5_60 <=> ! [X37] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.59  fof(f3160,plain,(
% 0.21/0.59    spl5_65 <=> k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.21/0.59  fof(f3382,plain,(
% 0.21/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60 | ~spl5_65)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f3381])).
% 0.21/0.59  fof(f3381,plain,(
% 0.21/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60 | ~spl5_65)),
% 0.21/0.59    inference(forward_demodulation,[],[f3380,f75])).
% 0.21/0.59  fof(f75,plain,(
% 0.21/0.59    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl5_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f74])).
% 0.21/0.59  fof(f3380,plain,(
% 0.21/0.59    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60 | ~spl5_65)),
% 0.21/0.59    inference(forward_demodulation,[],[f3379,f1811])).
% 0.21/0.59  fof(f1811,plain,(
% 0.21/0.59    ( ! [X24] : (k7_relat_1(sK0,X24) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X24)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60)),
% 0.21/0.59    inference(forward_demodulation,[],[f1788,f1670])).
% 0.21/0.59  fof(f1670,plain,(
% 0.21/0.59    ( ! [X33] : (k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,X33))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60)),
% 0.21/0.59    inference(subsumption_resolution,[],[f1590,f1578])).
% 0.21/0.59  fof(f1578,plain,(
% 0.21/0.59    ( ! [X37] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37)))) ) | ~spl5_60),
% 0.21/0.59    inference(avatar_component_clause,[],[f1577])).
% 0.21/0.59  fof(f1590,plain,(
% 0.21/0.59    ( ! [X33] : (k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,X33)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1589,f1462])).
% 0.21/0.59  fof(f1462,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(superposition,[],[f179,f1413])).
% 0.21/0.59  fof(f1413,plain,(
% 0.21/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(forward_demodulation,[],[f1410,f75])).
% 0.21/0.59  fof(f1410,plain,(
% 0.21/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) ) | ~spl5_4),
% 0.21/0.59    inference(resolution,[],[f247,f83])).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    v1_relat_1(sK1) | ~spl5_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f82])).
% 0.21/0.59  fof(f247,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~v1_relat_1(X2) | k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(X2)))) = k7_relat_1(X2,X3)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f245,f94])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.59    inference(global_subsumption,[],[f49,f48,f68])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.59    inference(equality_resolution,[],[f58])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(rectify,[],[f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(flattening,[],[f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(flattening,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f245,plain,(
% 0.21/0.59    ( ! [X2,X3] : (k7_relat_1(X2,k1_relat_1(k6_relat_1(X3))) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(X2)))) | ~v1_relat_1(X2)) )),
% 0.21/0.59    inference(resolution,[],[f50,f48])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.21/0.59  fof(f179,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(resolution,[],[f141,f48])).
% 0.21/0.59  fof(f141,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(resolution,[],[f134,f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.59  fof(f134,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(forward_demodulation,[],[f131,f75])).
% 0.21/0.59  fof(f131,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | ~spl5_4),
% 0.21/0.59    inference(resolution,[],[f56,f83])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(flattening,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.59  fof(f1589,plain,(
% 0.21/0.59    ( ! [X33] : (k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1588,f179])).
% 0.21/0.59  fof(f1588,plain,(
% 0.21/0.59    ( ! [X33] : (k1_relat_1(k7_relat_1(sK0,X33)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0))))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1587,f1462])).
% 0.21/0.59  fof(f1587,plain,(
% 0.21/0.59    ( ! [X33] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,X33))) | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1586,f1462])).
% 0.21/0.59  fof(f1586,plain,(
% 0.21/0.59    ( ! [X33] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))) | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1585,f179])).
% 0.21/0.59  fof(f1585,plain,(
% 0.21/0.59    ( ! [X33] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))))) | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1440,f1462])).
% 0.21/0.59  fof(f1440,plain,(
% 0.21/0.59    ( ! [X33] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X33)),k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0)))) | k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X33),k1_relat_1(sK0)))),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X33))) ) | ~spl5_6),
% 0.21/0.59    inference(superposition,[],[f1222,f1411])).
% 0.21/0.59  fof(f1411,plain,(
% 0.21/0.59    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK0))))) ) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f247,f91])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    v1_relat_1(sK0) | ~spl5_6),
% 0.21/0.59    inference(avatar_component_clause,[],[f90])).
% 0.21/0.59  fof(f1222,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) | k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) ) | ~spl5_6),
% 0.21/0.59    inference(forward_demodulation,[],[f1207,f94])).
% 0.21/0.59  fof(f1207,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK0,X0)))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | ~spl5_6),
% 0.21/0.59    inference(superposition,[],[f1010,f107])).
% 0.21/0.59  fof(f107,plain,(
% 0.21/0.59    ( ! [X2,X3] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X3) | ~r1_tarski(X2,X3)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f105,f94])).
% 0.21/0.59  fof(f105,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(k6_relat_1(X2)),X3) | k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X3)) )),
% 0.21/0.59    inference(resolution,[],[f57,f48])).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(flattening,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.59  fof(f1010,plain,(
% 0.21/0.59    ( ! [X9] : (k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK0,X9))),k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK0)))))) ) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f135,f502])).
% 0.21/0.59  fof(f502,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))),k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f331,f48])).
% 0.21/0.59  fof(f331,plain,(
% 0.21/0.59    ( ! [X7] : (~v1_relat_1(k6_relat_1(X7)) | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(sK0))),k1_relat_1(k7_relat_1(sK0,X7)))) ) | ~spl5_6),
% 0.21/0.59    inference(superposition,[],[f54,f260])).
% 0.21/0.59  fof(f260,plain,(
% 0.21/0.59    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl5_6),
% 0.21/0.59    inference(forward_demodulation,[],[f250,f94])).
% 0.21/0.59  fof(f250,plain,(
% 0.21/0.59    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0)))))) ) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f244,f48])).
% 0.21/0.59  fof(f244,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(X1,k1_relat_1(sK0)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(sK0,k1_relat_1(X1))))) ) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f50,f91])).
% 0.21/0.59  fof(f135,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = X2) )),
% 0.21/0.59    inference(forward_demodulation,[],[f133,f94])).
% 0.21/0.59  fof(f133,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(k6_relat_1(X3))) | k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = X2) )),
% 0.21/0.59    inference(resolution,[],[f56,f48])).
% 0.21/0.59  fof(f1788,plain,(
% 0.21/0.59    ( ! [X24] : (k7_relat_1(sK0,X24) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X24)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(superposition,[],[f1411,f1462])).
% 0.21/0.59  fof(f3379,plain,(
% 0.21/0.59    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60 | ~spl5_65)),
% 0.21/0.59    inference(forward_demodulation,[],[f3371,f1812])).
% 0.21/0.59  fof(f1812,plain,(
% 0.21/0.59    ( ! [X25] : (k7_relat_1(sK1,X25) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X25)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60)),
% 0.21/0.59    inference(forward_demodulation,[],[f1789,f1670])).
% 0.21/0.59  fof(f1789,plain,(
% 0.21/0.59    ( ! [X25] : (k7_relat_1(sK1,X25) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X25)))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(superposition,[],[f1413,f1462])).
% 0.21/0.59  fof(f3371,plain,(
% 0.21/0.59    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_65),
% 0.21/0.59    inference(trivial_inequality_removal,[],[f3370])).
% 0.21/0.59  fof(f3370,plain,(
% 0.21/0.59    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_65),
% 0.21/0.59    inference(superposition,[],[f53,f3161])).
% 0.21/0.59  fof(f3161,plain,(
% 0.21/0.59    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl5_65),
% 0.21/0.59    inference(avatar_component_clause,[],[f3160])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(rectify,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 0.21/0.59  fof(f3163,plain,(
% 0.21/0.59    spl5_65 | spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_51 | ~spl5_60),
% 0.21/0.59    inference(avatar_split_clause,[],[f3119,f1577,f881,f90,f82,f74,f70,f3160])).
% 0.21/0.59  fof(f881,plain,(
% 0.21/0.59    spl5_51 <=> ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.21/0.59  fof(f3119,plain,(
% 0.21/0.59    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_51 | ~spl5_60)),
% 0.21/0.59    inference(resolution,[],[f3089,f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f28,f27,f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f12])).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,negated_conjecture,(
% 0.21/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.59    inference(negated_conjecture,[],[f10])).
% 0.21/0.59  fof(f10,conjecture,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 0.21/0.59  fof(f3089,plain,(
% 0.21/0.59    ( ! [X9] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9) | k7_relat_1(sK0,X9) = k7_relat_1(sK1,X9)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_51 | ~spl5_60)),
% 0.21/0.59    inference(forward_demodulation,[],[f3088,f1811])).
% 0.21/0.59  fof(f3088,plain,(
% 0.21/0.59    ( ! [X9] : (k7_relat_1(sK1,X9) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X9))) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_51 | ~spl5_60)),
% 0.21/0.59    inference(forward_demodulation,[],[f3053,f1812])).
% 0.21/0.59  fof(f3053,plain,(
% 0.21/0.59    ( ! [X9] : (k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X9))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X9))) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X9))),X9)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_51 | ~spl5_60)),
% 0.21/0.59    inference(resolution,[],[f882,f1813])).
% 0.21/0.59  fof(f1813,plain,(
% 0.21/0.59    ( ! [X28,X29] : (~r2_hidden(X29,k1_relat_1(k7_relat_1(sK0,X28))) | r2_hidden(X29,X28)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_60)),
% 0.21/0.59    inference(forward_demodulation,[],[f1792,f1670])).
% 0.21/0.59  fof(f1792,plain,(
% 0.21/0.59    ( ! [X28,X29] : (~r2_hidden(X29,k1_relat_1(k7_relat_1(sK1,X28))) | r2_hidden(X29,X28)) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.59    inference(superposition,[],[f193,f1462])).
% 0.21/0.59  fof(f193,plain,(
% 0.21/0.59    ( ! [X6,X4,X5] : (~r2_hidden(X4,k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) | r2_hidden(X4,X5)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f191,f94])).
% 0.21/0.59  fof(f191,plain,(
% 0.21/0.59    ( ! [X6,X4,X5] : (~r2_hidden(X4,k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) | r2_hidden(X4,k1_relat_1(k6_relat_1(X5)))) )),
% 0.21/0.59    inference(resolution,[],[f63,f48])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f40])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.59    inference(flattening,[],[f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.59    inference(nnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.59  fof(f882,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl5_51),
% 0.21/0.59    inference(avatar_component_clause,[],[f881])).
% 0.21/0.59  fof(f1579,plain,(
% 0.21/0.59    ~spl5_6 | spl5_60 | ~spl5_2 | ~spl5_4 | ~spl5_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f1575,f90,f82,f74,f1577,f90])).
% 0.21/0.59  fof(f1575,plain,(
% 0.21/0.59    ( ! [X37] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(sK1,X37))) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.59    inference(forward_demodulation,[],[f1443,f1462])).
% 0.21/0.59  fof(f1443,plain,(
% 0.21/0.59    ( ! [X37] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X37)),k1_relat_1(k7_relat_1(k6_relat_1(X37),k1_relat_1(sK0)))) | ~v1_relat_1(sK0)) ) | ~spl5_6),
% 0.21/0.59    inference(superposition,[],[f54,f1411])).
% 0.21/0.59  fof(f883,plain,(
% 0.21/0.59    ~spl5_6 | spl5_51 | ~spl5_50),
% 0.21/0.59    inference(avatar_split_clause,[],[f873,f866,f881,f90])).
% 0.21/0.59  fof(f866,plain,(
% 0.21/0.59    spl5_50 <=> ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.21/0.59  fof(f873,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | ~spl5_50),
% 0.21/0.59    inference(resolution,[],[f867,f55])).
% 0.21/0.59  fof(f867,plain,(
% 0.21/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)) ) | ~spl5_50),
% 0.21/0.59    inference(avatar_component_clause,[],[f866])).
% 0.21/0.59  fof(f868,plain,(
% 0.21/0.59    spl5_50 | ~spl5_6 | ~spl5_5 | ~spl5_39),
% 0.21/0.59    inference(avatar_split_clause,[],[f864,f557,f86,f90,f866])).
% 0.21/0.59  fof(f557,plain,(
% 0.21/0.59    spl5_39 <=> ! [X1,X0] : (~r1_tarski(X1,k1_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(X0,sK1,X1),X1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.59  fof(f864,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | r2_hidden(sK3(sK0,sK1,X1),X1)) ) | (~spl5_5 | ~spl5_39)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f862])).
% 0.21/0.59  fof(f862,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1)) ) | (~spl5_5 | ~spl5_39)),
% 0.21/0.59    inference(resolution,[],[f558,f87])).
% 0.21/0.59  fof(f87,plain,(
% 0.21/0.59    v1_funct_1(sK0) | ~spl5_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f86])).
% 0.21/0.59  fof(f558,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(X0,sK1,X1),X1)) ) | ~spl5_39),
% 0.21/0.59    inference(avatar_component_clause,[],[f557])).
% 0.21/0.59  fof(f559,plain,(
% 0.21/0.59    ~spl5_4 | spl5_39 | ~spl5_2 | ~spl5_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f555,f78,f74,f557,f82])).
% 0.21/0.59  fof(f555,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(X0,sK1,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.59    inference(forward_demodulation,[],[f552,f75])).
% 0.21/0.59  fof(f552,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,sK1,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK1)) | ~r1_tarski(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_3),
% 0.21/0.59    inference(resolution,[],[f52,f79])).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    v1_funct_1(sK1) | ~spl5_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f78])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f33])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    spl5_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f41,f90])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    v1_relat_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f88,plain,(
% 0.21/0.59    spl5_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f42,f86])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    v1_funct_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    spl5_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f43,f82])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    v1_relat_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    spl5_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f44,f78])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    v1_funct_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    spl5_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f45,f74])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f72,plain,(
% 0.21/0.59    ~spl5_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f47,f70])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (10838)------------------------------
% 0.21/0.59  % (10838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (10838)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (10838)Memory used [KB]: 12665
% 0.21/0.59  % (10838)Time elapsed: 0.143 s
% 0.21/0.59  % (10838)------------------------------
% 0.21/0.59  % (10838)------------------------------
% 0.21/0.59  % (10831)Success in time 0.224 s
%------------------------------------------------------------------------------
