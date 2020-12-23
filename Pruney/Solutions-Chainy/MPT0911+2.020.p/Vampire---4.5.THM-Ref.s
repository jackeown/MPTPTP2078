%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 353 expanded)
%              Number of leaves         :   38 ( 140 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 ( 973 expanded)
%              Number of equality atoms :  162 ( 458 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f166,f302,f664,f705,f760,f805,f976,f1027,f1028,f1034,f1037,f1044,f1046,f1063,f1075,f1110,f1118,f1124,f1126,f1143,f1535])).

fof(f1535,plain,
    ( spl6_54
    | ~ spl6_61
    | ~ spl6_37
    | ~ spl6_45
    | ~ spl6_52
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f1530,f1103,f646,f597,f535,f745,f661])).

fof(f661,plain,
    ( spl6_54
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f745,plain,
    ( spl6_61
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f535,plain,
    ( spl6_37
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

% (30690)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f597,plain,
    ( spl6_45
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f646,plain,
    ( spl6_52
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1103,plain,
    ( spl6_70
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1530,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | sK3 = k2_mcart_1(sK4)
    | ~ spl6_37
    | ~ spl6_45
    | ~ spl6_52
    | ~ spl6_70 ),
    inference(resolution,[],[f1522,f537])).

fof(f537,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f535])).

fof(f1522,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK2)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X8)
        | sK3 = X8 )
    | ~ spl6_45
    | ~ spl6_52
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f1517,f1105])).

fof(f1105,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1517,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK2)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X8)
        | sK3 = X8 )
    | ~ spl6_45
    | ~ spl6_52 ),
    inference(resolution,[],[f825,f599])).

fof(f599,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f597])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK2)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1)
        | sK3 = X1 )
    | ~ spl6_52 ),
    inference(resolution,[],[f648,f63])).

fof(f63,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f30,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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

fof(f648,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f646])).

fof(f1143,plain,
    ( spl6_61
    | ~ spl6_62
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1138,f107,f749,f745])).

fof(f749,plain,
    ( spl6_62
  <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f107,plain,
    ( spl6_6
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1138,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl6_6 ),
    inference(resolution,[],[f109,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f109,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1126,plain,(
    spl6_62 ),
    inference(avatar_contradiction_clause,[],[f1125])).

fof(f1125,plain,
    ( $false
    | spl6_62 ),
    inference(resolution,[],[f751,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f751,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl6_62 ),
    inference(avatar_component_clause,[],[f749])).

fof(f1124,plain,
    ( spl6_39
    | spl6_4
    | spl6_2
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f1119,f99,f89,f84,f94,f552])).

fof(f552,plain,
    ( spl6_39
  <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f94,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f84,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f89,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f99,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1119,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | ~ spl6_5 ),
    inference(resolution,[],[f64,f101])).

fof(f101,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

% (30692)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f12,axiom,(
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

fof(f1118,plain,(
    spl6_71 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | spl6_71 ),
    inference(resolution,[],[f1109,f42])).

fof(f1109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_71 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1107,plain,
    ( spl6_71
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f1110,plain,
    ( spl6_70
    | ~ spl6_71
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f1091,f350,f1107,f1103])).

fof(f350,plain,
    ( spl6_25
  <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1091,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl6_25 ),
    inference(resolution,[],[f352,f45])).

fof(f352,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f350])).

fof(f1075,plain,
    ( spl6_52
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1072,f377,f646])).

fof(f377,plain,
    ( spl6_28
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1072,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f379,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f379,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f377])).

fof(f1063,plain,
    ( spl6_45
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f1061,f372,f597])).

fof(f372,plain,
    ( spl6_27
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1061,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl6_27 ),
    inference(resolution,[],[f374,f47])).

fof(f374,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f372])).

fof(f1046,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f1045,f99,f111,f107])).

fof(f111,plain,
    ( spl6_7
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1045,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1044,plain,
    ( spl6_37
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f1042,f359,f535])).

fof(f359,plain,
    ( spl6_26
  <=> r2_hidden(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1042,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl6_26 ),
    inference(resolution,[],[f361,f47])).

fof(f361,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f359])).

fof(f1037,plain,
    ( spl6_25
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f346,f107,f350])).

fof(f346,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1034,plain,
    ( spl6_26
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f355,f107,f359])).

fof(f355,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f51,f109])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1028,plain,
    ( spl6_27
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f367,f350,f372])).

fof(f367,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl6_25 ),
    inference(resolution,[],[f352,f51])).

fof(f1027,plain,
    ( spl6_28
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f368,f350,f377])).

fof(f368,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl6_25 ),
    inference(resolution,[],[f352,f50])).

fof(f976,plain,
    ( spl6_4
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | spl6_4
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f968])).

fof(f968,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_4
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(superposition,[],[f96,f909])).

fof(f909,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f907])).

fof(f907,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X0 )
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(superposition,[],[f251,f183])).

fof(f183,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f172,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_13
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f172,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4) ),
    inference(superposition,[],[f75,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f55,f49])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f75,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f251,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_16
  <=> ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f96,plain,
    ( k1_xboole_0 != sK0
    | spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f805,plain,
    ( spl6_14
    | spl6_3
    | spl6_4
    | spl6_16
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f804,f246,f162,f250,f94,f89,f243])).

fof(f243,plain,
    ( spl6_14
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f246,plain,
    ( spl6_15
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f804,plain,
    ( ! [X8,X9] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X9)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 )
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f783,f183])).

fof(f783,plain,
    ( ! [X8,X9] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8),X9)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 )
    | ~ spl6_15 ),
    inference(superposition,[],[f71,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f246])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f760,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f759,f111,f118])).

fof(f118,plain,
    ( spl6_8
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f759,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f113,f104])).

fof(f104,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f113,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f705,plain,
    ( spl6_14
    | spl6_2
    | spl6_15
    | spl6_16
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f704,f162,f118,f250,f246,f84,f243])).

fof(f704,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13 )
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f679,f183])).

fof(f679,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13 )
    | ~ spl6_8 ),
    inference(superposition,[],[f71,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f664,plain,
    ( ~ spl6_54
    | spl6_1
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f659,f552,f79,f661])).

fof(f79,plain,
    ( spl6_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f659,plain,
    ( sK3 != k2_mcart_1(sK4)
    | spl6_1
    | ~ spl6_39 ),
    inference(superposition,[],[f81,f554])).

fof(f554,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f552])).

fof(f81,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f302,plain,
    ( spl6_4
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl6_4
    | ~ spl6_14 ),
    inference(trivial_inequality_removal,[],[f294])).

fof(f294,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_4
    | ~ spl6_14 ),
    inference(superposition,[],[f96,f244])).

fof(f244,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f166,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f157,f162])).

fof(f157,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f74,f74])).

fof(f102,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f62,f99])).

fof(f62,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f32,f94])).

fof(f32,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (30657)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30673)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (30669)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (30657)Refutation not found, incomplete strategy% (30657)------------------------------
% 0.21/0.51  % (30657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30657)Memory used [KB]: 10746
% 0.21/0.51  % (30657)Time elapsed: 0.091 s
% 0.21/0.51  % (30657)------------------------------
% 0.21/0.51  % (30657)------------------------------
% 0.21/0.51  % (30659)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30658)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (30668)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (30671)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (30655)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (30684)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (30664)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (30664)Refutation not found, incomplete strategy% (30664)------------------------------
% 0.21/0.52  % (30664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30664)Memory used [KB]: 10618
% 0.21/0.52  % (30664)Time elapsed: 0.108 s
% 0.21/0.52  % (30664)------------------------------
% 0.21/0.52  % (30664)------------------------------
% 0.21/0.52  % (30656)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30661)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (30679)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (30674)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (30678)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (30665)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (30682)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (30678)Refutation not found, incomplete strategy% (30678)------------------------------
% 0.21/0.53  % (30678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30678)Memory used [KB]: 1791
% 0.21/0.53  % (30678)Time elapsed: 0.083 s
% 0.21/0.53  % (30678)------------------------------
% 0.21/0.53  % (30678)------------------------------
% 0.21/0.53  % (30660)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (30655)Refutation not found, incomplete strategy% (30655)------------------------------
% 0.21/0.53  % (30655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30655)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30655)Memory used [KB]: 1663
% 0.21/0.53  % (30655)Time elapsed: 0.128 s
% 0.21/0.53  % (30655)------------------------------
% 0.21/0.53  % (30655)------------------------------
% 0.21/0.54  % (30666)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30677)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (30662)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (30660)Refutation not found, incomplete strategy% (30660)------------------------------
% 0.21/0.54  % (30660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30660)Memory used [KB]: 6396
% 0.21/0.54  % (30660)Time elapsed: 0.133 s
% 0.21/0.54  % (30660)------------------------------
% 0.21/0.54  % (30660)------------------------------
% 0.21/0.54  % (30667)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (30675)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (30670)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (30672)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (30680)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (30672)Refutation not found, incomplete strategy% (30672)------------------------------
% 0.21/0.55  % (30672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30672)Memory used [KB]: 10618
% 0.21/0.55  % (30672)Time elapsed: 0.142 s
% 0.21/0.55  % (30672)------------------------------
% 0.21/0.55  % (30672)------------------------------
% 0.21/0.55  % (30675)Refutation not found, incomplete strategy% (30675)------------------------------
% 0.21/0.55  % (30675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30675)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30675)Memory used [KB]: 10746
% 0.21/0.55  % (30675)Time elapsed: 0.143 s
% 0.21/0.55  % (30675)------------------------------
% 0.21/0.55  % (30675)------------------------------
% 0.21/0.55  % (30676)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (30676)Refutation not found, incomplete strategy% (30676)------------------------------
% 0.21/0.55  % (30676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30676)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30676)Memory used [KB]: 1791
% 0.21/0.55  % (30676)Time elapsed: 0.141 s
% 0.21/0.55  % (30676)------------------------------
% 0.21/0.55  % (30676)------------------------------
% 0.21/0.55  % (30663)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (30663)Refutation not found, incomplete strategy% (30663)------------------------------
% 0.21/0.56  % (30663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30663)Memory used [KB]: 10746
% 0.21/0.56  % (30663)Time elapsed: 0.143 s
% 0.21/0.56  % (30663)------------------------------
% 0.21/0.56  % (30663)------------------------------
% 1.58/0.56  % (30665)Refutation not found, incomplete strategy% (30665)------------------------------
% 1.58/0.56  % (30665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (30665)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (30665)Memory used [KB]: 10618
% 1.58/0.56  % (30665)Time elapsed: 0.153 s
% 1.58/0.56  % (30665)------------------------------
% 1.58/0.56  % (30665)------------------------------
% 1.58/0.56  % (30683)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.56  % (30677)Refutation not found, incomplete strategy% (30677)------------------------------
% 1.58/0.56  % (30677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (30677)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (30677)Memory used [KB]: 10746
% 1.58/0.56  % (30677)Time elapsed: 0.158 s
% 1.58/0.56  % (30677)------------------------------
% 1.58/0.56  % (30677)------------------------------
% 1.71/0.58  % (30681)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.71/0.62  % (30671)Refutation found. Thanks to Tanya!
% 1.71/0.62  % SZS status Theorem for theBenchmark
% 2.04/0.63  % SZS output start Proof for theBenchmark
% 2.04/0.63  fof(f1541,plain,(
% 2.04/0.63    $false),
% 2.04/0.63    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f166,f302,f664,f705,f760,f805,f976,f1027,f1028,f1034,f1037,f1044,f1046,f1063,f1075,f1110,f1118,f1124,f1126,f1143,f1535])).
% 2.04/0.63  fof(f1535,plain,(
% 2.04/0.63    spl6_54 | ~spl6_61 | ~spl6_37 | ~spl6_45 | ~spl6_52 | ~spl6_70),
% 2.04/0.63    inference(avatar_split_clause,[],[f1530,f1103,f646,f597,f535,f745,f661])).
% 2.04/0.63  fof(f661,plain,(
% 2.04/0.63    spl6_54 <=> sK3 = k2_mcart_1(sK4)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 2.04/0.63  fof(f745,plain,(
% 2.04/0.63    spl6_61 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 2.04/0.63  fof(f535,plain,(
% 2.04/0.63    spl6_37 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.04/0.63  % (30690)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.63  fof(f597,plain,(
% 2.04/0.63    spl6_45 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.04/0.63  fof(f646,plain,(
% 2.04/0.63    spl6_52 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 2.04/0.63  fof(f1103,plain,(
% 2.04/0.63    spl6_70 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 2.04/0.63  fof(f1530,plain,(
% 2.04/0.63    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | (~spl6_37 | ~spl6_45 | ~spl6_52 | ~spl6_70)),
% 2.04/0.63    inference(resolution,[],[f1522,f537])).
% 2.04/0.63  fof(f537,plain,(
% 2.04/0.63    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl6_37),
% 2.04/0.63    inference(avatar_component_clause,[],[f535])).
% 2.04/0.63  fof(f1522,plain,(
% 2.04/0.63    ( ! [X8] : (~m1_subset_1(X8,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X8) | sK3 = X8) ) | (~spl6_45 | ~spl6_52 | ~spl6_70)),
% 2.04/0.63    inference(forward_demodulation,[],[f1517,f1105])).
% 2.04/0.63  fof(f1105,plain,(
% 2.04/0.63    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl6_70),
% 2.04/0.63    inference(avatar_component_clause,[],[f1103])).
% 2.04/0.63  fof(f1517,plain,(
% 2.04/0.63    ( ! [X8] : (~m1_subset_1(X8,sK2) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X8) | sK3 = X8) ) | (~spl6_45 | ~spl6_52)),
% 2.04/0.63    inference(resolution,[],[f825,f599])).
% 2.04/0.63  fof(f599,plain,(
% 2.04/0.63    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl6_45),
% 2.04/0.63    inference(avatar_component_clause,[],[f597])).
% 2.04/0.63  fof(f825,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK2) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1) | sK3 = X1) ) | ~spl6_52),
% 2.04/0.63    inference(resolution,[],[f648,f63])).
% 2.04/0.63  fof(f63,plain,(
% 2.04/0.63    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7) )),
% 2.04/0.63    inference(definition_unfolding,[],[f30,f48])).
% 2.04/0.63  fof(f48,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f5])).
% 2.04/0.63  fof(f5,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.04/0.63  fof(f30,plain,(
% 2.04/0.63    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 2.04/0.63    inference(cnf_transformation,[],[f19])).
% 2.04/0.63  fof(f19,plain,(
% 2.04/0.63    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.04/0.63    inference(flattening,[],[f18])).
% 2.04/0.63  fof(f18,plain,(
% 2.04/0.63    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.04/0.63    inference(ennf_transformation,[],[f16])).
% 2.04/0.63  fof(f16,negated_conjecture,(
% 2.04/0.63    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.04/0.63    inference(negated_conjecture,[],[f15])).
% 2.04/0.63  fof(f15,conjecture,(
% 2.04/0.63    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.04/0.63  fof(f648,plain,(
% 2.04/0.63    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl6_52),
% 2.04/0.63    inference(avatar_component_clause,[],[f646])).
% 2.04/0.63  fof(f1143,plain,(
% 2.04/0.63    spl6_61 | ~spl6_62 | ~spl6_6),
% 2.04/0.63    inference(avatar_split_clause,[],[f1138,f107,f749,f745])).
% 2.04/0.63  fof(f749,plain,(
% 2.04/0.63    spl6_62 <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.04/0.63  fof(f107,plain,(
% 2.04/0.63    spl6_6 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.04/0.63  fof(f1138,plain,(
% 2.04/0.63    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl6_6),
% 2.04/0.63    inference(resolution,[],[f109,f45])).
% 2.04/0.63  fof(f45,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 2.04/0.63    inference(cnf_transformation,[],[f24])).
% 2.04/0.63  fof(f24,plain,(
% 2.04/0.63    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(flattening,[],[f23])).
% 2.04/0.63  fof(f23,plain,(
% 2.04/0.63    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f10])).
% 2.04/0.63  fof(f10,axiom,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 2.04/0.63  fof(f109,plain,(
% 2.04/0.63    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_6),
% 2.04/0.63    inference(avatar_component_clause,[],[f107])).
% 2.04/0.63  fof(f1126,plain,(
% 2.04/0.63    spl6_62),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f1125])).
% 2.04/0.63  fof(f1125,plain,(
% 2.04/0.63    $false | spl6_62),
% 2.04/0.63    inference(resolution,[],[f751,f42])).
% 2.04/0.63  fof(f42,plain,(
% 2.04/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f4])).
% 2.04/0.63  fof(f4,axiom,(
% 2.04/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.04/0.63  fof(f751,plain,(
% 2.04/0.63    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl6_62),
% 2.04/0.63    inference(avatar_component_clause,[],[f749])).
% 2.04/0.63  fof(f1124,plain,(
% 2.04/0.63    spl6_39 | spl6_4 | spl6_2 | spl6_3 | ~spl6_5),
% 2.04/0.63    inference(avatar_split_clause,[],[f1119,f99,f89,f84,f94,f552])).
% 2.04/0.63  fof(f552,plain,(
% 2.04/0.63    spl6_39 <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.04/0.63  fof(f94,plain,(
% 2.04/0.63    spl6_4 <=> k1_xboole_0 = sK0),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.04/0.63  fof(f84,plain,(
% 2.04/0.63    spl6_2 <=> k1_xboole_0 = sK2),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.04/0.63  fof(f89,plain,(
% 2.04/0.63    spl6_3 <=> k1_xboole_0 = sK1),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.04/0.63  fof(f99,plain,(
% 2.04/0.63    spl6_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.04/0.63  fof(f1119,plain,(
% 2.04/0.63    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | ~spl6_5),
% 2.04/0.63    inference(resolution,[],[f64,f101])).
% 2.04/0.63  fof(f101,plain,(
% 2.04/0.63    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_5),
% 2.04/0.63    inference(avatar_component_clause,[],[f99])).
% 2.04/0.63  fof(f64,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 2.04/0.63    inference(definition_unfolding,[],[f54,f49])).
% 2.04/0.63  fof(f49,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f6])).
% 2.04/0.63  fof(f6,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.04/0.63  fof(f54,plain,(
% 2.04/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f29])).
% 2.04/0.63  fof(f29,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.04/0.63    inference(ennf_transformation,[],[f12])).
% 2.04/0.64  % (30692)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.04/0.64  fof(f1118,plain,(
% 2.04/0.64    spl6_71),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f1117])).
% 2.04/0.64  fof(f1117,plain,(
% 2.04/0.64    $false | spl6_71),
% 2.04/0.64    inference(resolution,[],[f1109,f42])).
% 2.04/0.64  fof(f1109,plain,(
% 2.04/0.64    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_71),
% 2.04/0.64    inference(avatar_component_clause,[],[f1107])).
% 2.04/0.64  fof(f1107,plain,(
% 2.04/0.64    spl6_71 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.04/0.64  fof(f1110,plain,(
% 2.04/0.64    spl6_70 | ~spl6_71 | ~spl6_25),
% 2.04/0.64    inference(avatar_split_clause,[],[f1091,f350,f1107,f1103])).
% 2.04/0.64  fof(f350,plain,(
% 2.04/0.64    spl6_25 <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.04/0.64  fof(f1091,plain,(
% 2.04/0.64    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl6_25),
% 2.04/0.64    inference(resolution,[],[f352,f45])).
% 2.04/0.64  fof(f352,plain,(
% 2.04/0.64    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_25),
% 2.04/0.64    inference(avatar_component_clause,[],[f350])).
% 2.04/0.64  fof(f1075,plain,(
% 2.04/0.64    spl6_52 | ~spl6_28),
% 2.04/0.64    inference(avatar_split_clause,[],[f1072,f377,f646])).
% 2.04/0.64  fof(f377,plain,(
% 2.04/0.64    spl6_28 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.04/0.64  fof(f1072,plain,(
% 2.04/0.64    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl6_28),
% 2.04/0.64    inference(resolution,[],[f379,f47])).
% 2.04/0.64  fof(f47,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f27])).
% 2.04/0.64  fof(f27,plain,(
% 2.04/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f2])).
% 2.04/0.64  fof(f2,axiom,(
% 2.04/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 2.04/0.64  fof(f379,plain,(
% 2.04/0.64    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl6_28),
% 2.04/0.64    inference(avatar_component_clause,[],[f377])).
% 2.04/0.64  fof(f1063,plain,(
% 2.04/0.64    spl6_45 | ~spl6_27),
% 2.04/0.64    inference(avatar_split_clause,[],[f1061,f372,f597])).
% 2.04/0.64  fof(f372,plain,(
% 2.04/0.64    spl6_27 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.04/0.64  fof(f1061,plain,(
% 2.04/0.64    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl6_27),
% 2.04/0.64    inference(resolution,[],[f374,f47])).
% 2.04/0.64  fof(f374,plain,(
% 2.04/0.64    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl6_27),
% 2.04/0.64    inference(avatar_component_clause,[],[f372])).
% 2.04/0.64  fof(f1046,plain,(
% 2.04/0.64    spl6_6 | spl6_7 | ~spl6_5),
% 2.04/0.64    inference(avatar_split_clause,[],[f1045,f99,f111,f107])).
% 2.04/0.64  fof(f111,plain,(
% 2.04/0.64    spl6_7 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.04/0.64  fof(f1045,plain,(
% 2.04/0.64    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_5),
% 2.04/0.64    inference(resolution,[],[f101,f46])).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f26])).
% 2.04/0.64  fof(f26,plain,(
% 2.04/0.64    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.04/0.64    inference(flattening,[],[f25])).
% 2.04/0.64  fof(f25,plain,(
% 2.04/0.64    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f3])).
% 2.04/0.64  fof(f3,axiom,(
% 2.04/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.04/0.64  fof(f1044,plain,(
% 2.04/0.64    spl6_37 | ~spl6_26),
% 2.04/0.64    inference(avatar_split_clause,[],[f1042,f359,f535])).
% 2.04/0.64  fof(f359,plain,(
% 2.04/0.64    spl6_26 <=> r2_hidden(k2_mcart_1(sK4),sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.04/0.64  fof(f1042,plain,(
% 2.04/0.64    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl6_26),
% 2.04/0.64    inference(resolution,[],[f361,f47])).
% 2.04/0.64  fof(f361,plain,(
% 2.04/0.64    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl6_26),
% 2.04/0.64    inference(avatar_component_clause,[],[f359])).
% 2.04/0.64  fof(f1037,plain,(
% 2.04/0.64    spl6_25 | ~spl6_6),
% 2.04/0.64    inference(avatar_split_clause,[],[f346,f107,f350])).
% 2.04/0.64  fof(f346,plain,(
% 2.04/0.64    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_6),
% 2.04/0.64    inference(resolution,[],[f109,f50])).
% 2.04/0.64  fof(f50,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f28])).
% 2.04/0.64  fof(f28,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.04/0.64    inference(ennf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.04/0.64  fof(f1034,plain,(
% 2.04/0.64    spl6_26 | ~spl6_6),
% 2.04/0.64    inference(avatar_split_clause,[],[f355,f107,f359])).
% 2.04/0.64  fof(f355,plain,(
% 2.04/0.64    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl6_6),
% 2.04/0.64    inference(resolution,[],[f51,f109])).
% 2.04/0.64  fof(f51,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f28])).
% 2.04/0.64  fof(f1028,plain,(
% 2.04/0.64    spl6_27 | ~spl6_25),
% 2.04/0.64    inference(avatar_split_clause,[],[f367,f350,f372])).
% 2.04/0.64  fof(f367,plain,(
% 2.04/0.64    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl6_25),
% 2.04/0.64    inference(resolution,[],[f352,f51])).
% 2.04/0.64  fof(f1027,plain,(
% 2.04/0.64    spl6_28 | ~spl6_25),
% 2.04/0.64    inference(avatar_split_clause,[],[f368,f350,f377])).
% 2.04/0.64  fof(f368,plain,(
% 2.04/0.64    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl6_25),
% 2.04/0.64    inference(resolution,[],[f352,f50])).
% 2.04/0.64  fof(f976,plain,(
% 2.04/0.64    spl6_4 | ~spl6_13 | ~spl6_16),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f975])).
% 2.04/0.64  fof(f975,plain,(
% 2.04/0.64    $false | (spl6_4 | ~spl6_13 | ~spl6_16)),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f968])).
% 2.04/0.64  fof(f968,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | (spl6_4 | ~spl6_13 | ~spl6_16)),
% 2.04/0.64    inference(superposition,[],[f96,f909])).
% 2.04/0.64  fof(f909,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = X0) ) | (~spl6_13 | ~spl6_16)),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f907])).
% 2.04/0.64  fof(f907,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0) ) | (~spl6_13 | ~spl6_16)),
% 2.04/0.64    inference(superposition,[],[f251,f183])).
% 2.04/0.64  fof(f183,plain,(
% 2.04/0.64    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) ) | ~spl6_13),
% 2.04/0.64    inference(forward_demodulation,[],[f172,f164])).
% 2.04/0.64  fof(f164,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl6_13),
% 2.04/0.64    inference(avatar_component_clause,[],[f162])).
% 2.04/0.64  fof(f162,plain,(
% 2.04/0.64    spl6_13 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.04/0.64  fof(f172,plain,(
% 2.04/0.64    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4)) )),
% 2.04/0.64    inference(superposition,[],[f75,f74])).
% 2.04/0.64  fof(f74,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.04/0.64    inference(equality_resolution,[],[f67])).
% 2.04/0.64  fof(f67,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 2.04/0.64    inference(definition_unfolding,[],[f60,f61])).
% 2.04/0.64  fof(f61,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f55,f49])).
% 2.04/0.64  fof(f55,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.04/0.64  fof(f60,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 | k1_xboole_0 != X3) )),
% 2.04/0.64    inference(cnf_transformation,[],[f13])).
% 2.04/0.64  fof(f13,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.04/0.64  fof(f75,plain,(
% 2.04/0.64    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.04/0.64    inference(equality_resolution,[],[f68])).
% 2.04/0.64  fof(f68,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X2) )),
% 2.04/0.64    inference(definition_unfolding,[],[f59,f61])).
% 2.04/0.64  fof(f59,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 | k1_xboole_0 != X2) )),
% 2.04/0.64    inference(cnf_transformation,[],[f13])).
% 2.04/0.64  fof(f251,plain,(
% 2.04/0.64    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1) ) | ~spl6_16),
% 2.04/0.64    inference(avatar_component_clause,[],[f250])).
% 2.04/0.64  fof(f250,plain,(
% 2.04/0.64    spl6_16 <=> ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.04/0.64  fof(f96,plain,(
% 2.04/0.64    k1_xboole_0 != sK0 | spl6_4),
% 2.04/0.64    inference(avatar_component_clause,[],[f94])).
% 2.04/0.64  fof(f805,plain,(
% 2.04/0.64    spl6_14 | spl6_3 | spl6_4 | spl6_16 | ~spl6_13 | ~spl6_15),
% 2.04/0.64    inference(avatar_split_clause,[],[f804,f246,f162,f250,f94,f89,f243])).
% 2.04/0.64  fof(f243,plain,(
% 2.04/0.64    spl6_14 <=> ! [X0] : k1_xboole_0 = X0),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.04/0.64  fof(f246,plain,(
% 2.04/0.64    spl6_15 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.04/0.64  fof(f804,plain,(
% 2.04/0.64    ( ! [X8,X9] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X9) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = X8 | k1_xboole_0 = X9) ) | (~spl6_13 | ~spl6_15)),
% 2.04/0.64    inference(forward_demodulation,[],[f783,f183])).
% 2.04/0.64  fof(f783,plain,(
% 2.04/0.64    ( ! [X8,X9] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8),X9) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = X8 | k1_xboole_0 = X9) ) | ~spl6_15),
% 2.04/0.64    inference(superposition,[],[f71,f248])).
% 2.04/0.64  fof(f248,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_15),
% 2.04/0.64    inference(avatar_component_clause,[],[f246])).
% 2.04/0.64  fof(f71,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 2.04/0.64    inference(definition_unfolding,[],[f56,f61])).
% 2.04/0.64  fof(f56,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 2.04/0.64    inference(cnf_transformation,[],[f13])).
% 2.04/0.64  fof(f760,plain,(
% 2.04/0.64    spl6_8 | ~spl6_7),
% 2.04/0.64    inference(avatar_split_clause,[],[f759,f111,f118])).
% 2.04/0.64  fof(f118,plain,(
% 2.04/0.64    spl6_8 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.04/0.64  fof(f759,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_7),
% 2.04/0.64    inference(resolution,[],[f113,f104])).
% 2.04/0.64  fof(f104,plain,(
% 2.04/0.64    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 2.04/0.64    inference(resolution,[],[f41,f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f21,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f17])).
% 2.04/0.64  fof(f17,plain,(
% 2.04/0.64    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.04/0.64    inference(unused_predicate_definition_removal,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.04/0.64  fof(f41,plain,(
% 2.04/0.64    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f22])).
% 2.04/0.64  fof(f22,plain,(
% 2.04/0.64    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.04/0.64    inference(ennf_transformation,[],[f11])).
% 2.04/0.64  fof(f11,axiom,(
% 2.04/0.64    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.04/0.64  fof(f113,plain,(
% 2.04/0.64    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_7),
% 2.04/0.64    inference(avatar_component_clause,[],[f111])).
% 2.04/0.64  fof(f705,plain,(
% 2.04/0.64    spl6_14 | spl6_2 | spl6_15 | spl6_16 | ~spl6_8 | ~spl6_13),
% 2.04/0.64    inference(avatar_split_clause,[],[f704,f162,f118,f250,f246,f84,f243])).
% 2.04/0.64  fof(f704,plain,(
% 2.04/0.64    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = X12 | k1_xboole_0 = X13) ) | (~spl6_8 | ~spl6_13)),
% 2.04/0.64    inference(forward_demodulation,[],[f679,f183])).
% 2.04/0.64  fof(f679,plain,(
% 2.04/0.64    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = X12 | k1_xboole_0 = X13) ) | ~spl6_8),
% 2.04/0.64    inference(superposition,[],[f71,f120])).
% 2.04/0.64  fof(f120,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_8),
% 2.04/0.64    inference(avatar_component_clause,[],[f118])).
% 2.04/0.64  fof(f664,plain,(
% 2.04/0.64    ~spl6_54 | spl6_1 | ~spl6_39),
% 2.04/0.64    inference(avatar_split_clause,[],[f659,f552,f79,f661])).
% 2.04/0.64  fof(f79,plain,(
% 2.04/0.64    spl6_1 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.04/0.64  fof(f659,plain,(
% 2.04/0.64    sK3 != k2_mcart_1(sK4) | (spl6_1 | ~spl6_39)),
% 2.04/0.64    inference(superposition,[],[f81,f554])).
% 2.04/0.64  fof(f554,plain,(
% 2.04/0.64    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | ~spl6_39),
% 2.04/0.64    inference(avatar_component_clause,[],[f552])).
% 2.04/0.64  fof(f81,plain,(
% 2.04/0.64    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) | spl6_1),
% 2.04/0.64    inference(avatar_component_clause,[],[f79])).
% 2.04/0.64  fof(f302,plain,(
% 2.04/0.64    spl6_4 | ~spl6_14),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f301])).
% 2.04/0.64  fof(f301,plain,(
% 2.04/0.64    $false | (spl6_4 | ~spl6_14)),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f294])).
% 2.04/0.64  fof(f294,plain,(
% 2.04/0.64    k1_xboole_0 != k1_xboole_0 | (spl6_4 | ~spl6_14)),
% 2.04/0.64    inference(superposition,[],[f96,f244])).
% 2.04/0.64  fof(f244,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl6_14),
% 2.04/0.64    inference(avatar_component_clause,[],[f243])).
% 2.04/0.64  fof(f166,plain,(
% 2.04/0.64    spl6_13),
% 2.04/0.64    inference(avatar_split_clause,[],[f157,f162])).
% 2.04/0.64  fof(f157,plain,(
% 2.04/0.64    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.04/0.64    inference(superposition,[],[f74,f74])).
% 2.04/0.64  fof(f102,plain,(
% 2.04/0.64    spl6_5),
% 2.04/0.64    inference(avatar_split_clause,[],[f62,f99])).
% 2.04/0.64  fof(f62,plain,(
% 2.04/0.64    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.64    inference(definition_unfolding,[],[f31,f49])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f97,plain,(
% 2.04/0.64    ~spl6_4),
% 2.04/0.64    inference(avatar_split_clause,[],[f32,f94])).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    k1_xboole_0 != sK0),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f92,plain,(
% 2.04/0.64    ~spl6_3),
% 2.04/0.64    inference(avatar_split_clause,[],[f33,f89])).
% 2.04/0.64  fof(f33,plain,(
% 2.04/0.64    k1_xboole_0 != sK1),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f87,plain,(
% 2.04/0.64    ~spl6_2),
% 2.04/0.64    inference(avatar_split_clause,[],[f34,f84])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    k1_xboole_0 != sK2),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f82,plain,(
% 2.04/0.64    ~spl6_1),
% 2.04/0.64    inference(avatar_split_clause,[],[f35,f79])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  % SZS output end Proof for theBenchmark
% 2.04/0.64  % (30671)------------------------------
% 2.04/0.64  % (30671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (30671)Termination reason: Refutation
% 2.04/0.64  
% 2.04/0.64  % (30671)Memory used [KB]: 11769
% 2.04/0.64  % (30671)Time elapsed: 0.189 s
% 2.04/0.64  % (30671)------------------------------
% 2.04/0.64  % (30671)------------------------------
% 2.04/0.64  % (30654)Success in time 0.269 s
%------------------------------------------------------------------------------
