%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0365+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 118 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 ( 531 expanded)
%              Number of equality atoms :   17 (  90 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3248,f3252,f3320])).

fof(f3320,plain,(
    ~ spl77_21 ),
    inference(avatar_contradiction_clause,[],[f3319])).

fof(f3319,plain,
    ( $false
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3318,f1056])).

fof(f1056,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f822])).

fof(f822,plain,
    ( sK5 != k3_subset_1(sK4,sK6)
    & r1_xboole_0(k3_subset_1(sK4,sK5),k3_subset_1(sK4,sK6))
    & r1_xboole_0(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f526,f821,f820])).

fof(f820,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK5 != k3_subset_1(sK4,X2)
          & r1_xboole_0(k3_subset_1(sK4,sK5),k3_subset_1(sK4,X2))
          & r1_xboole_0(sK5,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f821,plain,
    ( ? [X2] :
        ( sK5 != k3_subset_1(sK4,X2)
        & r1_xboole_0(k3_subset_1(sK4,sK5),k3_subset_1(sK4,X2))
        & r1_xboole_0(sK5,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK4)) )
   => ( sK5 != k3_subset_1(sK4,sK6)
      & r1_xboole_0(k3_subset_1(sK4,sK5),k3_subset_1(sK4,sK6))
      & r1_xboole_0(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f526,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f525])).

fof(f525,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f507])).

fof(f507,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f506])).

fof(f506,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(f3318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3317,f1057])).

fof(f1057,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f822])).

fof(f3317,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3316,f1058])).

fof(f1058,plain,(
    r1_xboole_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f822])).

fof(f3316,plain,
    ( ~ r1_xboole_0(sK5,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ spl77_21 ),
    inference(resolution,[],[f3290,f1257])).

fof(f1257,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f864])).

fof(f864,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f596])).

fof(f596,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f3290,plain,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK6))
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3288,f1922])).

fof(f1922,plain,(
    ~ sQ76_eqProxy(sK5,k3_subset_1(sK4,sK6)) ),
    inference(equality_proxy_replacement,[],[f1060,f1904])).

fof(f1904,plain,(
    ! [X1,X0] :
      ( sQ76_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ76_eqProxy])])).

fof(f1060,plain,(
    sK5 != k3_subset_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f822])).

fof(f3288,plain,
    ( sQ76_eqProxy(sK5,k3_subset_1(sK4,sK6))
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK6))
    | ~ spl77_21 ),
    inference(resolution,[],[f3270,f2063])).

fof(f2063,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | sQ76_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f1320,f1904])).

fof(f1320,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f899])).

fof(f899,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3270,plain,
    ( r1_tarski(k3_subset_1(sK4,sK6),sK5)
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3269,f1056])).

fof(f3269,plain,
    ( r1_tarski(k3_subset_1(sK4,sK6),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ spl77_21 ),
    inference(subsumption_resolution,[],[f3253,f1057])).

fof(f3253,plain,
    ( r1_tarski(k3_subset_1(sK4,sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ spl77_21 ),
    inference(resolution,[],[f3247,f1250])).

fof(f1250,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f591])).

fof(f591,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f590])).

fof(f590,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f498])).

fof(f498,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f3247,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),sK6)
    | ~ spl77_21 ),
    inference(avatar_component_clause,[],[f3245])).

fof(f3245,plain,
    ( spl77_21
  <=> r1_tarski(k3_subset_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_21])])).

fof(f3252,plain,(
    spl77_20 ),
    inference(avatar_contradiction_clause,[],[f3251])).

fof(f3251,plain,
    ( $false
    | spl77_20 ),
    inference(subsumption_resolution,[],[f3249,f1056])).

fof(f3249,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | spl77_20 ),
    inference(resolution,[],[f3243,f1232])).

fof(f1232,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f573])).

fof(f573,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3243,plain,
    ( ~ m1_subset_1(k3_subset_1(sK4,sK5),k1_zfmisc_1(sK4))
    | spl77_20 ),
    inference(avatar_component_clause,[],[f3241])).

fof(f3241,plain,
    ( spl77_20
  <=> m1_subset_1(k3_subset_1(sK4,sK5),k1_zfmisc_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_20])])).

fof(f3248,plain,
    ( ~ spl77_20
    | spl77_21 ),
    inference(avatar_split_clause,[],[f2446,f3245,f3241])).

fof(f2446,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),sK6)
    | ~ m1_subset_1(k3_subset_1(sK4,sK5),k1_zfmisc_1(sK4)) ),
    inference(subsumption_resolution,[],[f2438,f1057])).

fof(f2438,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(k3_subset_1(sK4,sK5),k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f1059,f1261])).

fof(f1261,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f866])).

fof(f866,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f505,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f1059,plain,(
    r1_xboole_0(k3_subset_1(sK4,sK5),k3_subset_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f822])).
%------------------------------------------------------------------------------
