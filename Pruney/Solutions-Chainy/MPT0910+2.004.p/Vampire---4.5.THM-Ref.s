%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 315 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  369 (1631 expanded)
%              Number of equality atoms :  180 ( 942 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f925,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f721,f727,f770,f821,f914])).

fof(f914,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f858,f720])).

fof(f720,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f719,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK4 != k6_mcart_1(sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK4 = X6
                | k3_mcart_1(X5,X6,X7) != sK5
                | ~ m1_subset_1(X7,sK3) )
            | ~ m1_subset_1(X6,sK2) )
        | ~ m1_subset_1(X5,sK1) )
    & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK4 != k6_mcart_1(sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK4 = X6
                  | k3_mcart_1(X5,X6,X7) != sK5
                  | ~ m1_subset_1(X7,sK3) )
              | ~ m1_subset_1(X6,sK2) )
          | ~ m1_subset_1(X5,sK1) )
      & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f719,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK1 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f718,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f718,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f717,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f717,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f706,f201])).

fof(f201,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f114,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f92,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f86,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f114,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f91,f93])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f706,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1 )
    | ~ spl9_2 ),
    inference(superposition,[],[f109,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f137,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
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

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f137,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl9_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f858,plain,
    ( k1_xboole_0 != sK4
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f56,f720])).

fof(f56,plain,(
    sK4 != k6_mcart_1(sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f821,plain,
    ( ~ spl9_1
    | ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f820])).

fof(f820,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f819,f298])).

fof(f298,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl9_1 ),
    inference(resolution,[],[f291,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f291,plain,
    ( r2_hidden(k2_mcart_1(sK5),sK3)
    | ~ spl9_1 ),
    inference(resolution,[],[f133,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f133,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl9_1
  <=> r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f819,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl9_1
    | ~ spl9_25 ),
    inference(trivial_inequality_removal,[],[f818])).

fof(f818,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl9_1
    | ~ spl9_25 ),
    inference(superposition,[],[f672,f296])).

fof(f296,plain,
    ( sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f293,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f293,plain,
    ( sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl9_1 ),
    inference(resolution,[],[f133,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f672,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl9_25
  <=> ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | ~ m1_subset_1(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f770,plain,(
    ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f768,f56])).

fof(f768,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK5)
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f767,f669])).

fof(f669,plain,
    ( sK4 = k2_mcart_1(k1_mcart_1(sK5))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl9_24
  <=> sK4 = k2_mcart_1(k1_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f767,plain,(
    k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f766,f53])).

fof(f766,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f765,f54])).

fof(f765,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f758,f55])).

fof(f758,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f102,f95])).

fof(f95,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f51,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f727,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f726,f135,f131])).

fof(f726,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(resolution,[],[f95,f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f721,plain,
    ( spl9_24
    | spl9_25
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f665,f131,f671,f667])).

fof(f665,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = k2_mcart_1(k1_mcart_1(sK5))
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f664,f333])).

fof(f333,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f311,f67])).

fof(f311,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f292,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,
    ( r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f133,f70])).

fof(f664,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = k2_mcart_1(k1_mcart_1(sK5))
        | ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f663,f317])).

fof(f317,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f310,f67])).

fof(f310,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f292,f71])).

fof(f663,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = k2_mcart_1(k1_mcart_1(sK5))
        | ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) )
    | ~ spl9_1 ),
    inference(superposition,[],[f94,f315])).

fof(f315,plain,
    ( k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f312,f63])).

fof(f312,plain,
    ( k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f292,f65])).

fof(f94,plain,(
    ! [X6,X7,X5] :
      ( sK5 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK4 = X6
      | ~ m1_subset_1(X7,sK3)
      | ~ m1_subset_1(X6,sK2)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f52,plain,(
    ! [X6,X7,X5] :
      ( sK4 = X6
      | k3_mcart_1(X5,X6,X7) != sK5
      | ~ m1_subset_1(X7,sK3)
      | ~ m1_subset_1(X6,sK2)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:34:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (5510)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (5527)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (5526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.50  % (5519)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (5498)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (5518)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (5510)Refutation not found, incomplete strategy% (5510)------------------------------
% 0.20/0.51  % (5510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5510)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5510)Memory used [KB]: 10618
% 0.20/0.51  % (5510)Time elapsed: 0.103 s
% 0.20/0.51  % (5510)------------------------------
% 0.20/0.51  % (5510)------------------------------
% 0.20/0.51  % (5508)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (5509)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (5527)Refutation not found, incomplete strategy% (5527)------------------------------
% 0.20/0.51  % (5527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5527)Memory used [KB]: 1663
% 0.20/0.51  % (5527)Time elapsed: 0.003 s
% 0.20/0.51  % (5527)------------------------------
% 0.20/0.51  % (5527)------------------------------
% 0.20/0.52  % (5504)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5525)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (5520)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (5526)Refutation not found, incomplete strategy% (5526)------------------------------
% 0.20/0.52  % (5526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5526)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5526)Memory used [KB]: 10874
% 0.20/0.52  % (5526)Time elapsed: 0.118 s
% 0.20/0.52  % (5526)------------------------------
% 0.20/0.52  % (5526)------------------------------
% 0.20/0.52  % (5517)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (5500)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (5502)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (5512)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (5499)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (5499)Refutation not found, incomplete strategy% (5499)------------------------------
% 0.20/0.53  % (5499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5499)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5499)Memory used [KB]: 1663
% 0.20/0.53  % (5499)Time elapsed: 0.125 s
% 0.20/0.53  % (5499)------------------------------
% 0.20/0.53  % (5499)------------------------------
% 0.20/0.53  % (5512)Refutation not found, incomplete strategy% (5512)------------------------------
% 0.20/0.53  % (5512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5512)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5512)Memory used [KB]: 1791
% 0.20/0.53  % (5512)Time elapsed: 0.093 s
% 0.20/0.53  % (5512)------------------------------
% 0.20/0.53  % (5512)------------------------------
% 0.20/0.53  % (5524)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (5503)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (5524)Refutation not found, incomplete strategy% (5524)------------------------------
% 0.20/0.53  % (5524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5524)Memory used [KB]: 6268
% 0.20/0.53  % (5524)Time elapsed: 0.128 s
% 0.20/0.53  % (5524)------------------------------
% 0.20/0.53  % (5524)------------------------------
% 0.20/0.53  % (5501)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (5513)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (5508)Refutation not found, incomplete strategy% (5508)------------------------------
% 0.20/0.53  % (5508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5508)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5508)Memory used [KB]: 10874
% 0.20/0.53  % (5508)Time elapsed: 0.109 s
% 0.20/0.53  % (5508)------------------------------
% 0.20/0.53  % (5508)------------------------------
% 0.20/0.54  % (5514)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (5525)Refutation not found, incomplete strategy% (5525)------------------------------
% 0.20/0.54  % (5525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5525)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5525)Memory used [KB]: 6268
% 0.20/0.54  % (5525)Time elapsed: 0.143 s
% 0.20/0.54  % (5525)------------------------------
% 0.20/0.54  % (5525)------------------------------
% 0.20/0.54  % (5514)Refutation not found, incomplete strategy% (5514)------------------------------
% 0.20/0.54  % (5514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5514)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5514)Memory used [KB]: 10618
% 0.20/0.54  % (5514)Time elapsed: 0.137 s
% 0.20/0.54  % (5514)------------------------------
% 0.20/0.54  % (5514)------------------------------
% 0.20/0.54  % (5505)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (5506)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (5516)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (5516)Refutation not found, incomplete strategy% (5516)------------------------------
% 0.20/0.54  % (5516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5516)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5516)Memory used [KB]: 1663
% 0.20/0.54  % (5516)Time elapsed: 0.138 s
% 0.20/0.54  % (5516)------------------------------
% 0.20/0.54  % (5516)------------------------------
% 0.20/0.54  % (5521)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (5523)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (5511)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (5507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (5522)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (5522)Refutation not found, incomplete strategy% (5522)------------------------------
% 0.20/0.55  % (5522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5522)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5522)Memory used [KB]: 10746
% 0.20/0.55  % (5522)Time elapsed: 0.149 s
% 0.20/0.55  % (5522)------------------------------
% 0.20/0.55  % (5522)------------------------------
% 0.20/0.55  % (5515)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.58  % (5504)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f925,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f721,f727,f770,f821,f914])).
% 0.20/0.58  fof(f914,plain,(
% 0.20/0.58    ~spl9_2),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f913])).
% 0.20/0.58  fof(f913,plain,(
% 0.20/0.58    $false | ~spl9_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f858,f720])).
% 0.20/0.58  fof(f720,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl9_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f719,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    k1_xboole_0 != sK1),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    sK4 != k6_mcart_1(sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5] : (! [X6] : (! [X7] : (sK4 = X6 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3)) | ~m1_subset_1(X6,sK2)) | ~m1_subset_1(X5,sK1)) & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK4 != k6_mcart_1(sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5] : (! [X6] : (! [X7] : (sK4 = X6 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3)) | ~m1_subset_1(X6,sK2)) | ~m1_subset_1(X5,sK1)) & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.58    inference(flattening,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.58    inference(negated_conjecture,[],[f18])).
% 0.20/0.58  fof(f18,conjecture,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.20/0.58  fof(f719,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK1) ) | ~spl9_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f718,f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    k1_xboole_0 != sK2),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f718,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1) ) | ~spl9_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f717,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    k1_xboole_0 != sK3),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f717,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1) ) | ~spl9_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f706,f201])).
% 0.20/0.58  fof(f201,plain,(
% 0.20/0.58    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 0.20/0.58    inference(superposition,[],[f114,f113])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f105])).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f92,f93])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f86,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.58    inference(flattening,[],[f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.20/0.58  fof(f114,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 0.20/0.58    inference(equality_resolution,[],[f106])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f91,f93])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f50])).
% 0.20/0.58  fof(f706,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1) ) | ~spl9_2),
% 0.20/0.58    inference(superposition,[],[f109,f139])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) | ~spl9_2),
% 0.20/0.58    inference(resolution,[],[f137,f122])).
% 0.20/0.58  fof(f122,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 0.20/0.58    inference(resolution,[],[f60,f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(rectify,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.20/0.58  fof(f137,plain,(
% 0.20/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl9_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f135])).
% 0.20/0.58  fof(f135,plain,(
% 0.20/0.58    spl9_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f88,f93])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f50])).
% 0.20/0.58  fof(f858,plain,(
% 0.20/0.58    k1_xboole_0 != sK4 | ~spl9_2),
% 0.20/0.58    inference(backward_demodulation,[],[f56,f720])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    sK4 != k6_mcart_1(sK1,sK2,sK3,sK5)),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f821,plain,(
% 0.20/0.58    ~spl9_1 | ~spl9_25),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f820])).
% 0.20/0.58  fof(f820,plain,(
% 0.20/0.58    $false | (~spl9_1 | ~spl9_25)),
% 0.20/0.58    inference(subsumption_resolution,[],[f819,f298])).
% 0.20/0.58  fof(f298,plain,(
% 0.20/0.58    m1_subset_1(k2_mcart_1(sK5),sK3) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f291,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.58  fof(f291,plain,(
% 0.20/0.58    r2_hidden(k2_mcart_1(sK5),sK3) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f133,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.58  fof(f133,plain,(
% 0.20/0.58    r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl9_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f131])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    spl9_1 <=> r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.58  fof(f819,plain,(
% 0.20/0.58    ~m1_subset_1(k2_mcart_1(sK5),sK3) | (~spl9_1 | ~spl9_25)),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f818])).
% 0.20/0.58  fof(f818,plain,(
% 0.20/0.58    sK5 != sK5 | ~m1_subset_1(k2_mcart_1(sK5),sK3) | (~spl9_1 | ~spl9_25)),
% 0.20/0.58    inference(superposition,[],[f672,f296])).
% 0.20/0.58  fof(f296,plain,(
% 0.20/0.58    sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) | ~spl9_1),
% 0.20/0.58    inference(subsumption_resolution,[],[f293,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.58  fof(f293,plain,(
% 0.20/0.58    sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f133,f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(flattening,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.58  fof(f672,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | ~m1_subset_1(X0,sK3)) ) | ~spl9_25),
% 0.20/0.58    inference(avatar_component_clause,[],[f671])).
% 0.20/0.58  fof(f671,plain,(
% 0.20/0.58    spl9_25 <=> ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | ~m1_subset_1(X0,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.20/0.58  fof(f770,plain,(
% 0.20/0.58    ~spl9_24),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f769])).
% 0.20/0.58  fof(f769,plain,(
% 0.20/0.58    $false | ~spl9_24),
% 0.20/0.58    inference(subsumption_resolution,[],[f768,f56])).
% 0.20/0.58  fof(f768,plain,(
% 0.20/0.58    sK4 = k6_mcart_1(sK1,sK2,sK3,sK5) | ~spl9_24),
% 0.20/0.58    inference(forward_demodulation,[],[f767,f669])).
% 0.20/0.58  fof(f669,plain,(
% 0.20/0.58    sK4 = k2_mcart_1(k1_mcart_1(sK5)) | ~spl9_24),
% 0.20/0.58    inference(avatar_component_clause,[],[f667])).
% 0.20/0.58  fof(f667,plain,(
% 0.20/0.58    spl9_24 <=> sK4 = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.20/0.58  fof(f767,plain,(
% 0.20/0.58    k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.58    inference(subsumption_resolution,[],[f766,f53])).
% 0.20/0.58  fof(f766,plain,(
% 0.20/0.58    k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK1),
% 0.20/0.58    inference(subsumption_resolution,[],[f765,f54])).
% 0.20/0.58  fof(f765,plain,(
% 0.20/0.58    k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.58    inference(subsumption_resolution,[],[f758,f55])).
% 0.20/0.58  fof(f758,plain,(
% 0.20/0.58    k6_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.58    inference(resolution,[],[f102,f95])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.58    inference(definition_unfolding,[],[f51,f69])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f84,f69])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.58  fof(f727,plain,(
% 0.20/0.58    spl9_1 | spl9_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f726,f135,f131])).
% 0.20/0.58  fof(f726,plain,(
% 0.20/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.58    inference(resolution,[],[f95,f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(flattening,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.58  fof(f721,plain,(
% 0.20/0.58    spl9_24 | spl9_25 | ~spl9_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f665,f131,f671,f667])).
% 0.20/0.58  fof(f665,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = k2_mcart_1(k1_mcart_1(sK5)) | ~m1_subset_1(X0,sK3)) ) | ~spl9_1),
% 0.20/0.58    inference(subsumption_resolution,[],[f664,f333])).
% 0.20/0.58  fof(f333,plain,(
% 0.20/0.58    m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f311,f67])).
% 0.20/0.58  fof(f311,plain,(
% 0.20/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),sK1) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f292,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f292,plain,(
% 0.20/0.58    r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(sK1,sK2)) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f133,f70])).
% 0.20/0.58  fof(f664,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = k2_mcart_1(k1_mcart_1(sK5)) | ~m1_subset_1(X0,sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)) ) | ~spl9_1),
% 0.20/0.58    inference(subsumption_resolution,[],[f663,f317])).
% 0.20/0.58  fof(f317,plain,(
% 0.20/0.58    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f310,f67])).
% 0.20/0.58  fof(f310,plain,(
% 0.20/0.58    r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f292,f71])).
% 0.20/0.58  fof(f663,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = k2_mcart_1(k1_mcart_1(sK5)) | ~m1_subset_1(X0,sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)) ) | ~spl9_1),
% 0.20/0.58    inference(superposition,[],[f94,f315])).
% 0.20/0.58  fof(f315,plain,(
% 0.20/0.58    k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) | ~spl9_1),
% 0.20/0.58    inference(subsumption_resolution,[],[f312,f63])).
% 0.20/0.58  fof(f312,plain,(
% 0.20/0.58    k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | ~spl9_1),
% 0.20/0.58    inference(resolution,[],[f292,f65])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X6,X7,X5] : (sK5 != k4_tarski(k4_tarski(X5,X6),X7) | sK4 = X6 | ~m1_subset_1(X7,sK3) | ~m1_subset_1(X6,sK2) | ~m1_subset_1(X5,sK1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f52,f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ( ! [X6,X7,X5] : (sK4 = X6 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3) | ~m1_subset_1(X6,sK2) | ~m1_subset_1(X5,sK1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (5504)------------------------------
% 0.20/0.58  % (5504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (5504)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (5504)Memory used [KB]: 11001
% 0.20/0.58  % (5504)Time elapsed: 0.151 s
% 0.20/0.58  % (5504)------------------------------
% 0.20/0.58  % (5504)------------------------------
% 0.20/0.59  % (5497)Success in time 0.226 s
%------------------------------------------------------------------------------
