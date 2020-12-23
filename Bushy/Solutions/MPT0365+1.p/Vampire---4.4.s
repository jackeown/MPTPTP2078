%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t46_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 3.41s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  342 (2041 expanded)
%              Number of leaves         :   50 ( 568 expanded)
%              Depth                    :   27
%              Number of atoms          :  991 (9289 expanded)
%              Number of equality atoms :  111 (1273 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1060,f1076,f1183,f1394,f2192,f2203,f2490,f2504,f5549,f5609,f11759,f11763,f12683,f12802,f17698,f18671,f18773,f18895,f34331,f36376,f59915,f61446])).

fof(f61446,plain,
    ( spl8_133
    | ~ spl8_774
    | ~ spl8_776 ),
    inference(avatar_contradiction_clause,[],[f61445])).

fof(f61445,plain,
    ( $false
    | ~ spl8_133
    | ~ spl8_774
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f61434,f61078])).

fof(f61078,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f61075,f67])).

fof(f67,plain,(
    k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k3_subset_1(sK0,sK2) != sK1
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,X2) != sK1
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK2) != X1
        & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK2))
        & r1_xboole_0(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t46_subset_1)).

fof(f61075,plain,
    ( k3_subset_1(sK0,sK2) = sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl8_776 ),
    inference(resolution,[],[f61063,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d10_xboole_0)).

fof(f61063,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl8_776 ),
    inference(resolution,[],[f61059,f107])).

fof(f107,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d1_zfmisc_1)).

fof(f61059,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k3_subset_1(sK0,sK2)))
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f61048,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f61048,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k3_subset_1(sK0,sK2)))
    | r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl8_776 ),
    inference(resolution,[],[f27846,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d3_tarski)).

fof(f27846,plain,
    ( ! [X14] :
        ( r2_hidden(sK5(sK1,X14),k3_subset_1(sK0,sK2))
        | r2_hidden(sK1,k1_zfmisc_1(X14)) )
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f27759,f14555])).

fof(f14555,plain,(
    ! [X9] :
      ( m1_subset_1(sK5(sK1,X9),sK0)
      | r2_hidden(sK1,k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f13124,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f75,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t7_boole)).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d2_subset_1)).

fof(f13124,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK1,X4),sK0)
      | r2_hidden(sK1,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f12887,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f90,f106])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12887,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f63,f601])).

fof(f601,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | r2_hidden(X5,X7)
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f89,f135])).

fof(f135,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5)) ) ),
    inference(subsumption_resolution,[],[f133,f69])).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',fc1_subset_1)).

fof(f133,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | v1_xboole_0(k1_zfmisc_1(X5))
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f74,f107])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f27759,plain,
    ( ! [X14] :
        ( r2_hidden(sK5(sK1,X14),k3_subset_1(sK0,sK2))
        | ~ m1_subset_1(sK5(sK1,X14),sK0)
        | r2_hidden(sK1,k1_zfmisc_1(X14)) )
    | ~ spl8_776 ),
    inference(resolution,[],[f11762,f11214])).

fof(f11214,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK5(sK1,X9),sK2)
      | r2_hidden(sK1,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f1700,f11201])).

fof(f11201,plain,(
    k4_xboole_0(sK2,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f11199])).

fof(f11199,plain,
    ( k4_xboole_0(sK2,sK1) = sK2
    | k4_xboole_0(sK2,sK1) = sK2 ),
    inference(resolution,[],[f11197,f2871])).

fof(f2871,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK7(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f2869,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d5_xboole_0)).

fof(f2869,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK7(X1,X2,X1),X2)
      | ~ r2_hidden(sK7(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f2854])).

fof(f2854,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK7(X1,X2,X1),X2)
      | ~ r2_hidden(sK7(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f1514,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1514,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f101])).

fof(f11197,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK7(sK2,X9,sK2),sK1)
      | k4_xboole_0(sK2,X9) = sK2 ) ),
    inference(resolution,[],[f2855,f65])).

fof(f65,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f2855,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(X5,X3)
      | k4_xboole_0(X3,X4) = X3
      | ~ r2_hidden(sK7(X3,X4,X3),X5) ) ),
    inference(resolution,[],[f1514,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t3_xboole_0)).

fof(f1700,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(sK5(X11,X12),k4_xboole_0(X13,X11))
      | r2_hidden(X11,k1_zfmisc_1(X12)) ) ),
    inference(resolution,[],[f140,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f11762,plain,
    ( ! [X10] :
        ( r2_hidden(X10,sK2)
        | r2_hidden(X10,k3_subset_1(sK0,sK2))
        | ~ m1_subset_1(X10,sK0) )
    | ~ spl8_776 ),
    inference(avatar_component_clause,[],[f11761])).

fof(f11761,plain,
    ( spl8_776
  <=> ! [X10] :
        ( r2_hidden(X10,k3_subset_1(sK0,sK2))
        | r2_hidden(X10,sK2)
        | ~ m1_subset_1(X10,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_776])])).

fof(f61434,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl8_133
    | ~ spl8_774
    | ~ spl8_776 ),
    inference(resolution,[],[f61432,f91])).

fof(f61432,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1)
    | ~ spl8_133
    | ~ spl8_774
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f61430,f61214])).

fof(f61214,plain,
    ( m1_subset_1(sK5(k3_subset_1(sK0,sK2),sK1),sK0)
    | ~ spl8_776 ),
    inference(resolution,[],[f61186,f137])).

fof(f61186,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK0)
    | ~ spl8_776 ),
    inference(resolution,[],[f61077,f1233])).

fof(f1233,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK2))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f110,f1083])).

fof(f1083,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f64,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',d5_subset_1)).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f61077,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2))
    | ~ spl8_776 ),
    inference(subsumption_resolution,[],[f61073,f67])).

fof(f61073,plain,
    ( k3_subset_1(sK0,sK2) = sK1
    | r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2))
    | ~ spl8_776 ),
    inference(resolution,[],[f61063,f309])).

fof(f309,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | r2_hidden(sK5(X2,X1),X2) ) ),
    inference(resolution,[],[f88,f90])).

fof(f61430,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(k3_subset_1(sK0,sK2),sK1),sK0)
    | ~ spl8_133
    | ~ spl8_774
    | ~ spl8_776 ),
    inference(resolution,[],[f61272,f11758])).

fof(f11758,plain,
    ( ! [X9] :
        ( r2_hidden(X9,k3_subset_1(sK0,sK1))
        | r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0) )
    | ~ spl8_774 ),
    inference(avatar_component_clause,[],[f11757])).

fof(f11757,plain,
    ( spl8_774
  <=> ! [X9] :
        ( r2_hidden(X9,k3_subset_1(sK0,sK1))
        | r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_774])])).

fof(f61272,plain,
    ( ~ r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK1))
    | ~ spl8_133
    | ~ spl8_776 ),
    inference(resolution,[],[f61193,f5801])).

fof(f5801,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X0,k3_subset_1(sK0,sK1)) )
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f5800,f1314])).

fof(f1314,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl8_133 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f1313,plain,
    ( spl8_133
  <=> ~ v1_xboole_0(k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f5800,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X0,k3_subset_1(sK0,sK2))
      | v1_xboole_0(k3_subset_1(sK0,sK2)) ) ),
    inference(resolution,[],[f66,f178])).

fof(f178,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f80,f74])).

fof(f66,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f61193,plain,
    ( m1_subset_1(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2))
    | ~ spl8_776 ),
    inference(resolution,[],[f61077,f137])).

fof(f59915,plain,
    ( ~ spl8_174
    | spl8_483 ),
    inference(avatar_contradiction_clause,[],[f59914])).

fof(f59914,plain,
    ( $false
    | ~ spl8_174
    | ~ spl8_483 ),
    inference(subsumption_resolution,[],[f59836,f19425])).

fof(f19425,plain,
    ( m1_subset_1(sK4(sK1,sK0),sK0)
    | ~ spl8_483 ),
    inference(resolution,[],[f18837,f137])).

fof(f18837,plain,
    ( r2_hidden(sK4(sK1,sK0),sK0)
    | ~ spl8_483 ),
    inference(resolution,[],[f7477,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7477,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl8_483 ),
    inference(avatar_component_clause,[],[f7476])).

fof(f7476,plain,
    ( spl8_483
  <=> ~ r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_483])])).

fof(f59836,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0),sK0)
    | ~ spl8_174
    | ~ spl8_483 ),
    inference(resolution,[],[f2202,f18838])).

fof(f18838,plain,
    ( r2_hidden(sK4(sK1,sK0),sK1)
    | ~ spl8_483 ),
    inference(resolution,[],[f7477,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2202,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0) )
    | ~ spl8_174 ),
    inference(avatar_component_clause,[],[f2201])).

fof(f2201,plain,
    ( spl8_174
  <=> ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).

fof(f36376,plain,
    ( spl8_125
    | ~ spl8_458 ),
    inference(avatar_contradiction_clause,[],[f36372])).

fof(f36372,plain,
    ( $false
    | ~ spl8_125
    | ~ spl8_458 ),
    inference(resolution,[],[f35179,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',existence_m1_subset_1)).

fof(f35179,plain,
    ( ! [X10] : ~ m1_subset_1(X10,k3_subset_1(sK0,sK1))
    | ~ spl8_125
    | ~ spl8_458 ),
    inference(subsumption_resolution,[],[f35178,f2941])).

fof(f2941,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK1))
        | r2_hidden(X6,sK0) )
    | ~ spl8_125 ),
    inference(subsumption_resolution,[],[f2940,f1053])).

fof(f1053,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK1))
    | ~ spl8_125 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f1052,plain,
    ( spl8_125
  <=> ~ v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f2940,plain,(
    ! [X6] :
      ( v1_xboole_0(k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X6,k3_subset_1(sK0,sK1))
      | r2_hidden(X6,sK0) ) ),
    inference(forward_demodulation,[],[f2935,f1034])).

fof(f1034,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f85,f63])).

fof(f2935,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK1))
      | r2_hidden(X6,sK0)
      | v1_xboole_0(k4_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f147,f1034])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | v1_xboole_0(k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f110,f74])).

fof(f35178,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK0)
        | ~ m1_subset_1(X10,k3_subset_1(sK0,sK1)) )
    | ~ spl8_125
    | ~ spl8_458 ),
    inference(subsumption_resolution,[],[f35174,f1053])).

fof(f35174,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK0)
        | ~ m1_subset_1(X10,k3_subset_1(sK0,sK1))
        | v1_xboole_0(k3_subset_1(sK0,sK1)) )
    | ~ spl8_458 ),
    inference(resolution,[],[f7284,f178])).

fof(f7284,plain,
    ( r1_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl8_458 ),
    inference(avatar_component_clause,[],[f7283])).

fof(f7283,plain,
    ( spl8_458
  <=> r1_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_458])])).

fof(f34331,plain,
    ( spl8_28
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f34326,f334,f340])).

fof(f340,plain,
    ( spl8_28
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f334,plain,
    ( spl8_27
  <=> ~ r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f34326,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f64,f310])).

fof(f310,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f88,f135])).

fof(f18895,plain,
    ( spl8_7
    | ~ spl8_500 ),
    inference(avatar_contradiction_clause,[],[f18891])).

fof(f18891,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_500 ),
    inference(resolution,[],[f18715,f73])).

fof(f18715,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK2)
    | ~ spl8_7
    | ~ spl8_500 ),
    inference(subsumption_resolution,[],[f18714,f13145])).

fof(f13145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK0) )
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f13131,f195])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_7
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f13131,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f12896,f74])).

fof(f12896,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f64,f601])).

fof(f18714,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_7
    | ~ spl8_500 ),
    inference(subsumption_resolution,[],[f18712,f195])).

fof(f18712,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | v1_xboole_0(sK2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_500 ),
    inference(resolution,[],[f7788,f1959])).

fof(f1959,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X8,X7)
      | ~ m1_subset_1(X6,X8)
      | v1_xboole_0(X8)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f178,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',symmetry_r1_xboole_0)).

fof(f7788,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl8_500 ),
    inference(avatar_component_clause,[],[f7787])).

fof(f7787,plain,
    ( spl8_500
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_500])])).

fof(f18773,plain,
    ( spl8_24
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f18769,f321,f327])).

fof(f327,plain,
    ( spl8_24
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f321,plain,
    ( spl8_23
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f18769,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f63,f310])).

fof(f18671,plain,
    ( spl8_2
    | ~ spl8_483
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f8342,f615,f7476,f173])).

fof(f173,plain,
    ( spl8_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f615,plain,
    ( spl8_88
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f8342,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ spl8_88 ),
    inference(resolution,[],[f1552,f73])).

fof(f1552,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK1),X0)
        | ~ r1_xboole_0(X0,sK0)
        | v1_xboole_0(X0) )
    | ~ spl8_88 ),
    inference(resolution,[],[f925,f74])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1),X0)
        | ~ r1_xboole_0(X0,sK0) )
    | ~ spl8_88 ),
    inference(resolution,[],[f924,f80])).

fof(f924,plain,
    ( r2_hidden(sK3(sK1),sK0)
    | ~ spl8_88 ),
    inference(resolution,[],[f616,f73])).

fof(f616,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f615])).

fof(f17698,plain,
    ( spl8_2
    | spl8_88 ),
    inference(avatar_split_clause,[],[f1219,f615,f173])).

fof(f1219,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f602,f74])).

fof(f602,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK1)
      | r2_hidden(X8,sK0) ) ),
    inference(resolution,[],[f89,f157])).

fof(f157,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f153,f107])).

fof(f153,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f136,f63])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f135,f106])).

fof(f12802,plain,
    ( ~ spl8_92
    | spl8_501 ),
    inference(avatar_contradiction_clause,[],[f12801])).

fof(f12801,plain,
    ( $false
    | ~ spl8_92
    | ~ spl8_501 ),
    inference(subsumption_resolution,[],[f12481,f145])).

fof(f145,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(superposition,[],[f142,f113])).

fof(f113,plain,(
    ! [X0] : k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(backward_demodulation,[],[f111,f71])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t4_boole)).

fof(f111,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',dt_o_0_0_xboole_0)).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t6_boole)).

fof(f142,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f109,f127])).

fof(f127,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f106,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12481,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(sK2,sK2)),sK2),o_0_0_xboole_0)
    | ~ spl8_92
    | ~ spl8_501 ),
    inference(backward_demodulation,[],[f666,f11294])).

fof(f11294,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(sK2,sK2)),sK2),sK0)
    | ~ spl8_501 ),
    inference(resolution,[],[f11291,f603])).

fof(f603,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK2)
      | r2_hidden(X9,sK0) ) ),
    inference(resolution,[],[f89,f180])).

fof(f180,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f154,f107])).

fof(f154,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f136,f64])).

fof(f11291,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(sK2,sK2)),sK2),sK2)
    | ~ spl8_501 ),
    inference(resolution,[],[f9304,f127])).

fof(f9304,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK2),X0)
        | r2_hidden(sK4(X0,sK2),sK2) )
    | ~ spl8_501 ),
    inference(resolution,[],[f9228,f79])).

fof(f9228,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r2_hidden(sK4(sK2,sK2),X0) )
    | ~ spl8_501 ),
    inference(resolution,[],[f9223,f80])).

fof(f9223,plain,
    ( r2_hidden(sK4(sK2,sK2),sK2)
    | ~ spl8_501 ),
    inference(resolution,[],[f7924,f7797])).

fof(f7797,plain,
    ( r2_hidden(sK4(sK2,sK0),sK2)
    | ~ spl8_501 ),
    inference(resolution,[],[f7791,f78])).

fof(f7791,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl8_501 ),
    inference(avatar_component_clause,[],[f7790])).

fof(f7790,plain,
    ( spl8_501
  <=> ~ r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_501])])).

fof(f7924,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK0),X0)
        | r2_hidden(sK4(X0,sK2),sK2) )
    | ~ spl8_501 ),
    inference(resolution,[],[f7824,f79])).

fof(f7824,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r2_hidden(sK4(sK2,sK0),X0) )
    | ~ spl8_501 ),
    inference(resolution,[],[f7797,f80])).

fof(f666,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl8_92
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f12683,plain,
    ( ~ spl8_92
    | spl8_459 ),
    inference(avatar_contradiction_clause,[],[f12682])).

fof(f12682,plain,
    ( $false
    | ~ spl8_92
    | ~ spl8_459 ),
    inference(subsumption_resolution,[],[f12115,f145])).

fof(f12115,plain,
    ( r2_hidden(sK4(k3_subset_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl8_92
    | ~ spl8_459 ),
    inference(backward_demodulation,[],[f666,f7295])).

fof(f7295,plain,
    ( r2_hidden(sK4(k3_subset_1(sK0,sK1),sK0),sK0)
    | ~ spl8_459 ),
    inference(resolution,[],[f7294,f79])).

fof(f7294,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK1),sK0)
    | ~ spl8_459 ),
    inference(resolution,[],[f7287,f82])).

fof(f7287,plain,
    ( ~ r1_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl8_459 ),
    inference(avatar_component_clause,[],[f7286])).

fof(f7286,plain,
    ( spl8_459
  <=> ~ r1_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_459])])).

fof(f11763,plain,
    ( spl8_92
    | spl8_776 ),
    inference(avatar_split_clause,[],[f11748,f11761,f665])).

fof(f11748,plain,(
    ! [X10] :
      ( r2_hidden(X10,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X10,sK0)
      | r2_hidden(X10,sK2)
      | o_0_0_xboole_0 = sK0 ) ),
    inference(superposition,[],[f3019,f1083])).

fof(f3019,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(X15,k4_xboole_0(X16,X17))
      | ~ m1_subset_1(X15,X16)
      | r2_hidden(X15,X17)
      | o_0_0_xboole_0 = X16 ) ),
    inference(resolution,[],[f1264,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f111,f72])).

fof(f1264,plain,(
    ! [X4,X2,X3] :
      ( v1_xboole_0(X4)
      | r2_hidden(X2,k4_xboole_0(X4,X3))
      | ~ m1_subset_1(X2,X4)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f108,f74])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f11759,plain,
    ( spl8_92
    | spl8_774 ),
    inference(avatar_split_clause,[],[f11747,f11757,f665])).

fof(f11747,plain,(
    ! [X9] :
      ( r2_hidden(X9,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X9,sK0)
      | r2_hidden(X9,sK1)
      | o_0_0_xboole_0 = sK0 ) ),
    inference(superposition,[],[f3019,f1034])).

fof(f5609,plain,
    ( ~ spl8_126
    | ~ spl8_172 ),
    inference(avatar_contradiction_clause,[],[f5608])).

fof(f5608,plain,
    ( $false
    | ~ spl8_126
    | ~ spl8_172 ),
    inference(subsumption_resolution,[],[f1677,f2199])).

fof(f2199,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_172 ),
    inference(avatar_component_clause,[],[f2198])).

fof(f2198,plain,
    ( spl8_172
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_172])])).

fof(f1677,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_126 ),
    inference(resolution,[],[f1674,f97])).

fof(f1674,plain,
    ( r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl8_126 ),
    inference(resolution,[],[f1059,f73])).

fof(f1059,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_subset_1(sK0,sK1))
        | r2_hidden(X0,sK0) )
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1058,plain,
    ( spl8_126
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,k3_subset_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f5549,plain,
    ( ~ spl8_6
    | spl8_125
    | ~ spl8_126
    | spl8_173 ),
    inference(avatar_contradiction_clause,[],[f5548])).

fof(f5548,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_173 ),
    inference(subsumption_resolution,[],[f5545,f1681])).

fof(f1681,plain,
    ( m1_subset_1(sK3(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl8_126 ),
    inference(resolution,[],[f1674,f137])).

fof(f5545,plain,
    ( ~ m1_subset_1(sK3(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl8_6
    | ~ spl8_125
    | ~ spl8_173 ),
    inference(resolution,[],[f3903,f73])).

fof(f3903,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl8_6
    | ~ spl8_125
    | ~ spl8_173 ),
    inference(subsumption_resolution,[],[f3899,f1053])).

fof(f3899,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k3_subset_1(sK0,sK1))
        | v1_xboole_0(k3_subset_1(sK0,sK1)) )
    | ~ spl8_6
    | ~ spl8_173 ),
    inference(resolution,[],[f2618,f74])).

fof(f2618,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl8_6
    | ~ spl8_173 ),
    inference(subsumption_resolution,[],[f2617,f2196])).

fof(f2196,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_173 ),
    inference(avatar_component_clause,[],[f2195])).

fof(f2195,plain,
    ( spl8_173
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_173])])).

fof(f2617,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f2592,f178])).

fof(f2592,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),sK0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f2591,f2549])).

fof(f2549,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f2529,f114])).

fof(f114,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f111,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',t3_boole)).

fof(f2529,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = k4_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f2511,f1083])).

fof(f2511,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(resolution,[],[f198,f112])).

fof(f198,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2591,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,o_0_0_xboole_0))
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f66,f2511])).

fof(f2504,plain,
    ( spl8_6
    | spl8_94 ),
    inference(avatar_split_clause,[],[f1119,f680,f197])).

fof(f680,plain,
    ( spl8_94
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f1119,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f603,f74])).

fof(f2490,plain,
    ( spl8_7
    | ~ spl8_24
    | ~ spl8_94 ),
    inference(avatar_contradiction_clause,[],[f2489])).

fof(f2489,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_24
    | ~ spl8_94 ),
    inference(resolution,[],[f2443,f73])).

fof(f2443,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK2)
    | ~ spl8_7
    | ~ spl8_24
    | ~ spl8_94 ),
    inference(subsumption_resolution,[],[f2253,f681])).

fof(f681,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK0) )
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f680])).

fof(f2253,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f2252,f195])).

fof(f2252,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(sK2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f2245,f178])).

fof(f2245,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f65,f328])).

fof(f328,plain,
    ( sK0 = sK1
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f327])).

fof(f2203,plain,
    ( spl8_172
    | spl8_174
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f1960,f340,f2201,f2198])).

fof(f1960,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl8_28 ),
    inference(resolution,[],[f178,f1835])).

fof(f1835,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f341,f65])).

fof(f341,plain,
    ( sK0 = sK2
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f340])).

fof(f2192,plain,
    ( ~ spl8_2
    | spl8_23
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f2189])).

fof(f2189,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(resolution,[],[f2126,f2163])).

fof(f2163,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_2
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f2161,f2118])).

fof(f2118,plain,
    ( k3_subset_1(sK0,sK0) != o_0_0_xboole_0
    | ~ spl8_2
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f2069,f1842])).

fof(f1842,plain,
    ( k3_subset_1(sK0,sK0) != sK1
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f67,f341])).

fof(f2069,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(resolution,[],[f174,f112])).

fof(f174,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f173])).

fof(f2161,plain,
    ( k3_subset_1(sK0,sK0) = o_0_0_xboole_0
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_2 ),
    inference(superposition,[],[f84,f2136])).

fof(f2136,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK0
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f2092,f114])).

fof(f2092,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = k4_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2069,f1034])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',involutiveness_k3_subset_1)).

fof(f2126,plain,
    ( ! [X11] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X11))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f2069,f1977])).

fof(f1977,plain,
    ( ! [X11] : m1_subset_1(sK1,k1_zfmisc_1(X11))
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(resolution,[],[f1968,f137])).

fof(f1968,plain,
    ( ! [X1] : r2_hidden(sK1,k1_zfmisc_1(X1))
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1965,f1748])).

fof(f1748,plain,(
    ! [X9] :
      ( m1_subset_1(sK5(sK1,X9),sK0)
      | r2_hidden(sK1,k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f1707,f137])).

fof(f1707,plain,(
    ! [X25] :
      ( r2_hidden(sK5(sK1,X25),sK0)
      | r2_hidden(sK1,k1_zfmisc_1(X25)) ) ),
    inference(resolution,[],[f140,f602])).

fof(f1965,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK1,X1),sK0)
        | r2_hidden(sK1,k1_zfmisc_1(X1)) )
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(resolution,[],[f1962,f140])).

fof(f1962,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,sK1)
        | ~ m1_subset_1(X9,sK0) )
    | ~ spl8_23
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1960,f404])).

fof(f404,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_23 ),
    inference(resolution,[],[f395,f97])).

fof(f395,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | ~ spl8_23 ),
    inference(resolution,[],[f322,f90])).

fof(f322,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f321])).

fof(f1394,plain,
    ( spl8_27
    | ~ spl8_132 ),
    inference(avatar_contradiction_clause,[],[f1393])).

fof(f1393,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_132 ),
    inference(subsumption_resolution,[],[f1375,f138])).

fof(f138,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f137,f127])).

fof(f1375,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl8_27
    | ~ spl8_132 ),
    inference(backward_demodulation,[],[f1357,f398])).

fof(f398,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | ~ spl8_27 ),
    inference(resolution,[],[f335,f135])).

fof(f335,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1357,plain,
    ( sK0 = sK2
    | ~ spl8_132 ),
    inference(backward_demodulation,[],[f1339,f1335])).

fof(f1335,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK2
    | ~ spl8_132 ),
    inference(subsumption_resolution,[],[f1333,f64])).

fof(f1333,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_132 ),
    inference(superposition,[],[f84,f1326])).

fof(f1326,plain,
    ( k3_subset_1(sK0,sK2) = o_0_0_xboole_0
    | ~ spl8_132 ),
    inference(resolution,[],[f1317,f112])).

fof(f1317,plain,
    ( v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl8_132 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1316,plain,
    ( spl8_132
  <=> v1_xboole_0(k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f1339,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK0
    | ~ spl8_132 ),
    inference(forward_demodulation,[],[f1337,f114])).

fof(f1337,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = k4_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl8_132 ),
    inference(resolution,[],[f1336,f85])).

fof(f1336,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_132 ),
    inference(subsumption_resolution,[],[f1334,f64])).

fof(f1334,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_132 ),
    inference(superposition,[],[f83,f1326])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t46_subset_1.p',dt_k3_subset_1)).

fof(f1183,plain,
    ( spl8_23
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1182])).

fof(f1182,plain,
    ( $false
    | ~ spl8_23
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1160,f138])).

fof(f1160,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl8_23
    | ~ spl8_124 ),
    inference(backward_demodulation,[],[f1130,f396])).

fof(f396,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl8_23 ),
    inference(resolution,[],[f322,f135])).

fof(f1130,plain,
    ( sK0 = sK1
    | ~ spl8_124 ),
    inference(backward_demodulation,[],[f1102,f1073])).

fof(f1073,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK1
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1071,f63])).

fof(f1071,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_124 ),
    inference(superposition,[],[f84,f1065])).

fof(f1065,plain,
    ( k3_subset_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl8_124 ),
    inference(resolution,[],[f1056,f112])).

fof(f1056,plain,
    ( v1_xboole_0(k3_subset_1(sK0,sK1))
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl8_124
  <=> v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f1102,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK0
    | ~ spl8_124 ),
    inference(forward_demodulation,[],[f1100,f114])).

fof(f1100,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = k4_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl8_124 ),
    inference(resolution,[],[f1077,f85])).

fof(f1077,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1072,f63])).

fof(f1072,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_124 ),
    inference(superposition,[],[f83,f1065])).

fof(f1076,plain,
    ( ~ spl8_6
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1075])).

fof(f1075,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1074,f1043])).

fof(f1043,plain,
    ( sK0 != sK1
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f1041,f863])).

fof(f863,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) != sK1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f67,f687])).

fof(f687,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(resolution,[],[f198,f112])).

fof(f1041,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = sK0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f1035,f114])).

fof(f1035,plain,
    ( k3_subset_1(sK0,o_0_0_xboole_0) = k4_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f85,f688])).

fof(f688,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f687,f64])).

fof(f1074,plain,
    ( sK0 = sK1
    | ~ spl8_6
    | ~ spl8_124 ),
    inference(forward_demodulation,[],[f1073,f1041])).

fof(f1060,plain,
    ( spl8_124
    | spl8_126 ),
    inference(avatar_split_clause,[],[f1050,f1058,f1055])).

fof(f1050,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,k3_subset_1(sK0,sK1))
      | v1_xboole_0(k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1049,f74])).

fof(f1049,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f110,f1034])).
%------------------------------------------------------------------------------
