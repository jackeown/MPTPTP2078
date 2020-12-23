%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:13 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  199 (1620 expanded)
%              Number of leaves         :   25 ( 399 expanded)
%              Depth                    :   27
%              Number of atoms          :  609 (9074 expanded)
%              Number of equality atoms :  140 (2417 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f201,f230,f245,f264,f303,f344,f458,f472,f712])).

fof(f712,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f710,f696])).

% (2672)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f696,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f684,f694])).

fof(f694,plain,
    ( ! [X12] : k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f693,f516])).

fof(f516,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f52,f515])).

fof(f515,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f501,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f501,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f181,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f181,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_11
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f693,plain,
    ( ! [X12] :
        ( ~ v1_funct_1(k1_xboole_0)
        | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f692,f557])).

fof(f557,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f556,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f556,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0))
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f521,f515])).

fof(f521,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ r1_tarski(sK3,k7_relat_1(sK3,X0)) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f183,f515])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,k7_relat_1(sK3,X0))
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f148,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f148,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(resolution,[],[f131,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f131,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f692,plain,
    ( ! [X12,X11] :
        ( ~ v1_funct_1(k7_relat_1(k1_xboole_0,X11))
        | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f691,f557])).

fof(f691,plain,
    ( ! [X12,X10,X11] :
        ( ~ v1_funct_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11))
        | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f690,f515])).

fof(f690,plain,
    ( ! [X12,X10,X11] :
        ( k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f689,f557])).

fof(f689,plain,
    ( ! [X12,X10,X11] :
        ( k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f653,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f653,plain,
    ( ! [X12,X10,X11] :
        ( k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f652,f557])).

fof(f652,plain,
    ( ! [X12,X10,X11] :
        ( k7_relat_1(k7_relat_1(k1_xboole_0,X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k1_xboole_0,X11),X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f651,f557])).

fof(f651,plain,
    ( ! [X12,X10,X11] :
        ( k7_relat_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f511,f515])).

fof(f511,plain,
    ( ! [X12,X10,X11] :
        ( k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12)
        | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) )
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f413,f119])).

fof(f413,plain,(
    ! [X12,X10,X11] :
      ( k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12)
      | ~ v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11)) ) ),
    inference(resolution,[],[f347,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f347,plain,(
    ! [X8,X7] : m1_subset_1(k7_relat_1(k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f345,f346])).

fof(f346,plain,(
    ! [X6,X5] : k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6) ),
    inference(subsumption_resolution,[],[f189,f199])).

fof(f199,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f198,f52])).

fof(f198,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f197,f54])).

fof(f197,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f88,f142])).

fof(f142,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f136,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f87])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f189,plain,(
    ! [X6,X5] :
      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6)
      | ~ v1_funct_1(k7_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f147,f87])).

fof(f147,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f146,f142])).

fof(f146,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f345,plain,(
    ! [X8,X7] : m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f190,f199])).

fof(f190,plain,(
    ! [X8,X7] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X7)) ) ),
    inference(resolution,[],[f147,f89])).

fof(f684,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f683,f119])).

fof(f683,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f682,f515])).

fof(f682,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f681,f499])).

fof(f499,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f129,f119])).

fof(f129,plain,
    ( sK0 = sK2
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f681,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f106,f114])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f710,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f552,f114])).

fof(f552,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f498,f515])).

fof(f498,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f53,f119])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f472,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f352,f127,f123])).

fof(f123,plain,
    ( spl5_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f352,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f55,f69])).

fof(f55,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f458,plain,
    ( spl5_3
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl5_3
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f451,f145])).

fof(f145,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(backward_demodulation,[],[f110,f142])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f451,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl5_14 ),
    inference(superposition,[],[f213,f402])).

fof(f402,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_14 ),
    inference(resolution,[],[f366,f55])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f365,f131])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl5_14 ),
    inference(superposition,[],[f61,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f132,f244])).

fof(f244,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl5_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f132,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f54,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f213,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) ),
    inference(subsumption_resolution,[],[f212,f184])).

fof(f184,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f147,f78])).

fof(f212,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f207,f199])).

fof(f207,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f204,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f204,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f203,f184])).

fof(f203,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f186,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f186,plain,(
    ! [X2] : v5_relat_1(k7_relat_1(sK3,X2),sK1) ),
    inference(resolution,[],[f147,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f344,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f342,f293])).

fof(f293,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f266,f279])).

fof(f279,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(sK3,X0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f278,f58])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k7_relat_1(sK3,X0))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f277,f93])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k7_relat_1(sK3,X0))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f276,f119])).

fof(f276,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f261,f93])).

fof(f261,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = k2_zfmisc_1(k1_xboole_0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) )
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f205,f119])).

fof(f205,plain,(
    ! [X0] :
      ( k2_zfmisc_1(sK0,sK1) = k7_relat_1(sK3,X0)
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f191,f69])).

% (2666)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (2674)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (2670)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (2654)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (2671)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (2658)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (2673)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (2655)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (2661)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (2647)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f191,plain,(
    ! [X9] : r1_tarski(k7_relat_1(sK3,X9),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f147,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f266,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f254,f93])).

fof(f254,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f147,f119])).

fof(f342,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f335,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f335,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f298,f114])).

fof(f298,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f145,f279])).

fof(f303,plain,
    ( ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f301,f265])).

fof(f265,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f252,f93])).

fof(f252,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f138,f119])).

fof(f138,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f54,f73])).

fof(f301,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_5
    | spl5_11 ),
    inference(forward_demodulation,[],[f300,f279])).

fof(f300,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k7_relat_1(sK3,X0))
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f281,f270])).

fof(f270,plain,
    ( k1_xboole_0 != sK3
    | ~ spl5_5
    | spl5_11 ),
    inference(forward_demodulation,[],[f256,f93])).

fof(f256,plain,
    ( sK3 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl5_5
    | spl5_11 ),
    inference(backward_demodulation,[],[f180,f119])).

fof(f180,plain,
    ( sK3 != k2_zfmisc_1(sK0,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f281,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3
        | ~ r1_tarski(sK3,k7_relat_1(sK3,X0)) )
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f183,f279])).

fof(f264,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f249,f58])).

fof(f249,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5
    | spl5_6 ),
    inference(backward_demodulation,[],[f125,f119])).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f245,plain,
    ( spl5_14
    | spl5_4 ),
    inference(avatar_split_clause,[],[f139,f113,f242])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f134,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f54,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f230,plain,
    ( spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f226,f144])).

fof(f144,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(backward_demodulation,[],[f106,f142])).

fof(f226,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_4 ),
    inference(superposition,[],[f211,f214])).

fof(f214,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl5_4 ),
    inference(resolution,[],[f152,f55])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | spl5_4 ),
    inference(subsumption_resolution,[],[f151,f131])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | spl5_4 ),
    inference(superposition,[],[f61,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl5_4 ),
    inference(backward_demodulation,[],[f132,f140])).

fof(f140,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f139,f115])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f211,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f210,f184])).

fof(f210,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f206,f199])).

fof(f206,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f204,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f201,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f199,f143])).

fof(f143,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl5_1 ),
    inference(backward_demodulation,[],[f102,f142])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f120,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f56,f117,f113])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f57,f108,f104,f100])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (2675)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (2646)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2657)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (2649)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (2652)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (2668)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.54  % (2660)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.54  % (2651)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.55  % (2676)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.55  % (2669)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.55  % (2650)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.55  % (2645)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.55  % (2656)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.55  % (2665)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.55  % (2648)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.55  % (2644)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.56  % (2652)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f756,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f111,f120,f201,f230,f245,f264,f303,f344,f458,f472,f712])).
% 1.47/0.56  fof(f712,plain,(
% 1.47/0.56    spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f711])).
% 1.47/0.56  fof(f711,plain,(
% 1.47/0.56    $false | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f710,f696])).
% 1.47/0.56  % (2672)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  fof(f696,plain,(
% 1.47/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11)),
% 1.47/0.56    inference(backward_demodulation,[],[f684,f694])).
% 1.47/0.56  fof(f694,plain,(
% 1.47/0.56    ( ! [X12] : (k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f693,f516])).
% 1.47/0.56  fof(f516,plain,(
% 1.47/0.56    v1_funct_1(k1_xboole_0) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(backward_demodulation,[],[f52,f515])).
% 1.47/0.56  fof(f515,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f501,f93])).
% 1.47/0.56  fof(f93,plain,(
% 1.47/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.47/0.56    inference(equality_resolution,[],[f76])).
% 1.47/0.56  fof(f76,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.56    inference(flattening,[],[f49])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.47/0.56  fof(f501,plain,(
% 1.47/0.56    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(backward_demodulation,[],[f181,f119])).
% 1.47/0.56  fof(f119,plain,(
% 1.47/0.56    k1_xboole_0 = sK0 | ~spl5_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f117])).
% 1.47/0.56  fof(f117,plain,(
% 1.47/0.56    spl5_5 <=> k1_xboole_0 = sK0),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.47/0.56  fof(f181,plain,(
% 1.47/0.56    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl5_11),
% 1.47/0.56    inference(avatar_component_clause,[],[f179])).
% 1.47/0.56  fof(f179,plain,(
% 1.47/0.56    spl5_11 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    v1_funct_1(sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.47/0.56    inference(flattening,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.47/0.56    inference(ennf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.47/0.56    inference(negated_conjecture,[],[f17])).
% 1.47/0.56  fof(f17,conjecture,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.47/0.56  fof(f693,plain,(
% 1.47/0.56    ( ! [X12] : (~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f692,f557])).
% 1.47/0.56  fof(f557,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f556,f58])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.47/0.56  fof(f556,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0)) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f521,f515])).
% 1.47/0.56  fof(f521,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(backward_demodulation,[],[f183,f515])).
% 1.47/0.56  fof(f183,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(sK3,k7_relat_1(sK3,X0)) | sK3 = k7_relat_1(sK3,X0)) )),
% 1.47/0.56    inference(resolution,[],[f148,f69])).
% 1.47/0.56  fof(f69,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(flattening,[],[f42])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.56  fof(f148,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 1.47/0.56    inference(resolution,[],[f131,f60])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.47/0.56  fof(f131,plain,(
% 1.47/0.56    v1_relat_1(sK3)),
% 1.47/0.56    inference(resolution,[],[f54,f78])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f692,plain,(
% 1.47/0.56    ( ! [X12,X11] : (~v1_funct_1(k7_relat_1(k1_xboole_0,X11)) | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f691,f557])).
% 1.47/0.56  fof(f691,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (~v1_funct_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11)) | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12)) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f690,f515])).
% 1.47/0.56  fof(f690,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f689,f557])).
% 1.47/0.56  fof(f689,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f653,f114])).
% 1.47/0.56  fof(f114,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | ~spl5_4),
% 1.47/0.56    inference(avatar_component_clause,[],[f113])).
% 1.47/0.56  fof(f113,plain,(
% 1.47/0.56    spl5_4 <=> k1_xboole_0 = sK1),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.47/0.56  fof(f653,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k7_relat_1(k1_xboole_0,X12) = k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f652,f557])).
% 1.47/0.56  fof(f652,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k1_xboole_0,X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k1_xboole_0,X11),X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f651,f557])).
% 1.47/0.56  fof(f651,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(k1_xboole_0,X10),X11),X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f511,f515])).
% 1.47/0.56  fof(f511,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k2_partfun1(k1_xboole_0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) ) | ~spl5_5),
% 1.47/0.56    inference(backward_demodulation,[],[f413,f119])).
% 1.47/0.56  fof(f413,plain,(
% 1.47/0.56    ( ! [X12,X10,X11] : (k2_partfun1(sK0,sK1,k7_relat_1(k7_relat_1(sK3,X10),X11),X12) = k7_relat_1(k7_relat_1(k7_relat_1(sK3,X10),X11),X12) | ~v1_funct_1(k7_relat_1(k7_relat_1(sK3,X10),X11))) )),
% 1.47/0.56    inference(resolution,[],[f347,f87])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f36])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.47/0.56  fof(f347,plain,(
% 1.47/0.56    ( ! [X8,X7] : (m1_subset_1(k7_relat_1(k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.56    inference(backward_demodulation,[],[f345,f346])).
% 1.47/0.56  fof(f346,plain,(
% 1.47/0.56    ( ! [X6,X5] : (k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f189,f199])).
% 1.47/0.56  fof(f199,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f198,f52])).
% 1.47/0.56  fof(f198,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f197,f54])).
% 1.47/0.56  fof(f197,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.47/0.56    inference(superposition,[],[f88,f142])).
% 1.47/0.56  fof(f142,plain,(
% 1.47/0.56    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f136,f52])).
% 1.47/0.56  fof(f136,plain,(
% 1.47/0.56    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.47/0.56    inference(resolution,[],[f54,f87])).
% 1.47/0.56  fof(f88,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f38])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.47/0.56  fof(f189,plain,(
% 1.47/0.56    ( ! [X6,X5] : (k2_partfun1(sK0,sK1,k7_relat_1(sK3,X5),X6) = k7_relat_1(k7_relat_1(sK3,X5),X6) | ~v1_funct_1(k7_relat_1(sK3,X5))) )),
% 1.47/0.56    inference(resolution,[],[f147,f87])).
% 1.47/0.56  fof(f147,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.56    inference(forward_demodulation,[],[f146,f142])).
% 1.47/0.56  fof(f146,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f137,f52])).
% 1.47/0.56  fof(f137,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.47/0.56    inference(resolution,[],[f54,f89])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f38])).
% 1.47/0.56  fof(f345,plain,(
% 1.47/0.56    ( ! [X8,X7] : (m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f190,f199])).
% 1.47/0.56  fof(f190,plain,(
% 1.47/0.56    ( ! [X8,X7] : (m1_subset_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X7),X8),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k7_relat_1(sK3,X7))) )),
% 1.47/0.56    inference(resolution,[],[f147,f89])).
% 1.47/0.56  fof(f684,plain,(
% 1.47/0.56    ~v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f683,f119])).
% 1.47/0.56  fof(f683,plain,(
% 1.47/0.56    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f682,f515])).
% 1.47/0.56  fof(f682,plain,(
% 1.47/0.56    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.47/0.56    inference(forward_demodulation,[],[f681,f499])).
% 1.47/0.56  fof(f499,plain,(
% 1.47/0.56    k1_xboole_0 = sK2 | (~spl5_5 | ~spl5_7)),
% 1.47/0.56    inference(backward_demodulation,[],[f129,f119])).
% 1.47/0.56  fof(f129,plain,(
% 1.47/0.56    sK0 = sK2 | ~spl5_7),
% 1.47/0.56    inference(avatar_component_clause,[],[f127])).
% 1.47/0.56  fof(f127,plain,(
% 1.47/0.56    spl5_7 <=> sK0 = sK2),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.47/0.56  fof(f681,plain,(
% 1.47/0.56    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl5_2 | ~spl5_4)),
% 1.47/0.56    inference(forward_demodulation,[],[f106,f114])).
% 1.47/0.56  fof(f106,plain,(
% 1.47/0.56    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl5_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f104])).
% 1.47/0.56  fof(f104,plain,(
% 1.47/0.56    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.56  fof(f710,plain,(
% 1.47/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f552,f114])).
% 1.47/0.56  fof(f552,plain,(
% 1.47/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl5_5 | ~spl5_11)),
% 1.47/0.56    inference(backward_demodulation,[],[f498,f515])).
% 1.47/0.56  fof(f498,plain,(
% 1.47/0.56    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl5_5),
% 1.47/0.56    inference(backward_demodulation,[],[f53,f119])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f472,plain,(
% 1.47/0.56    ~spl5_6 | spl5_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f352,f127,f123])).
% 1.47/0.56  fof(f123,plain,(
% 1.47/0.56    spl5_6 <=> r1_tarski(sK0,sK2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.47/0.56  fof(f352,plain,(
% 1.47/0.56    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.47/0.56    inference(resolution,[],[f55,f69])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    r1_tarski(sK2,sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f458,plain,(
% 1.47/0.56    spl5_3 | ~spl5_14),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f457])).
% 1.47/0.56  fof(f457,plain,(
% 1.47/0.56    $false | (spl5_3 | ~spl5_14)),
% 1.47/0.56    inference(subsumption_resolution,[],[f451,f145])).
% 1.47/0.56  fof(f145,plain,(
% 1.47/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.47/0.56    inference(backward_demodulation,[],[f110,f142])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f108])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.47/0.56  fof(f451,plain,(
% 1.47/0.56    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl5_14),
% 1.47/0.56    inference(superposition,[],[f213,f402])).
% 1.47/0.56  fof(f402,plain,(
% 1.47/0.56    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl5_14),
% 1.47/0.56    inference(resolution,[],[f366,f55])).
% 1.47/0.56  fof(f366,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl5_14),
% 1.47/0.56    inference(subsumption_resolution,[],[f365,f131])).
% 1.47/0.56  fof(f365,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl5_14),
% 1.47/0.56    inference(superposition,[],[f61,f348])).
% 1.47/0.56  fof(f348,plain,(
% 1.47/0.56    sK0 = k1_relat_1(sK3) | ~spl5_14),
% 1.47/0.56    inference(backward_demodulation,[],[f132,f244])).
% 1.47/0.56  fof(f244,plain,(
% 1.47/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f242])).
% 1.47/0.56  fof(f242,plain,(
% 1.47/0.56    spl5_14 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.47/0.56  fof(f132,plain,(
% 1.47/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.47/0.56    inference(resolution,[],[f54,f79])).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.47/0.56  fof(f213,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f212,f184])).
% 1.47/0.56  fof(f184,plain,(
% 1.47/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.56    inference(resolution,[],[f147,f78])).
% 1.47/0.56  fof(f212,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f207,f199])).
% 1.47/0.56  fof(f207,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.47/0.56    inference(resolution,[],[f204,f66])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.47/0.56  fof(f204,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f203,f184])).
% 1.47/0.56  fof(f203,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.56    inference(resolution,[],[f186,f62])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.47/0.56  fof(f186,plain,(
% 1.47/0.56    ( ! [X2] : (v5_relat_1(k7_relat_1(sK3,X2),sK1)) )),
% 1.47/0.56    inference(resolution,[],[f147,f80])).
% 1.47/0.56  fof(f80,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.47/0.56    inference(pure_predicate_removal,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.56  fof(f344,plain,(
% 1.47/0.56    spl5_3 | ~spl5_4 | ~spl5_5),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f343])).
% 1.47/0.56  fof(f343,plain,(
% 1.47/0.56    $false | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f342,f293])).
% 1.47/0.56  fof(f293,plain,(
% 1.47/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl5_5),
% 1.47/0.56    inference(backward_demodulation,[],[f266,f279])).
% 1.47/0.56  fof(f279,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl5_5),
% 1.47/0.56    inference(subsumption_resolution,[],[f278,f58])).
% 1.47/0.56  fof(f278,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl5_5),
% 1.47/0.56    inference(forward_demodulation,[],[f277,f93])).
% 1.47/0.56  fof(f277,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl5_5),
% 1.47/0.56    inference(forward_demodulation,[],[f276,f119])).
% 1.47/0.56  fof(f276,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))) ) | ~spl5_5),
% 1.47/0.56    inference(forward_demodulation,[],[f261,f93])).
% 1.47/0.56  fof(f261,plain,(
% 1.47/0.56    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_zfmisc_1(k1_xboole_0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))) ) | ~spl5_5),
% 1.47/0.56    inference(backward_demodulation,[],[f205,f119])).
% 1.47/0.56  fof(f205,plain,(
% 1.47/0.56    ( ! [X0] : (k2_zfmisc_1(sK0,sK1) = k7_relat_1(sK3,X0) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k7_relat_1(sK3,X0))) )),
% 1.47/0.56    inference(resolution,[],[f191,f69])).
% 1.47/0.56  % (2666)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.56  % (2674)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.56  % (2670)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.56  % (2654)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.56  % (2671)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (2658)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.57  % (2673)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.57  % (2655)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.57  % (2661)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.57  % (2647)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.47/0.57  fof(f191,plain,(
% 1.47/0.57    ( ! [X9] : (r1_tarski(k7_relat_1(sK3,X9),k2_zfmisc_1(sK0,sK1))) )),
% 1.47/0.57    inference(resolution,[],[f147,f73])).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f48])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.57    inference(nnf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.57  fof(f266,plain,(
% 1.47/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_5),
% 1.47/0.57    inference(forward_demodulation,[],[f254,f93])).
% 1.47/0.57  fof(f254,plain,(
% 1.47/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | ~spl5_5),
% 1.47/0.57    inference(backward_demodulation,[],[f147,f119])).
% 1.47/0.57  fof(f342,plain,(
% 1.47/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.47/0.57    inference(forward_demodulation,[],[f335,f92])).
% 1.47/0.57  fof(f92,plain,(
% 1.47/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.47/0.57    inference(equality_resolution,[],[f77])).
% 1.47/0.57  fof(f77,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.47/0.57    inference(cnf_transformation,[],[f50])).
% 1.47/0.57  fof(f335,plain,(
% 1.47/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.47/0.57    inference(backward_demodulation,[],[f298,f114])).
% 1.47/0.57  fof(f298,plain,(
% 1.47/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl5_3 | ~spl5_5)),
% 1.47/0.57    inference(backward_demodulation,[],[f145,f279])).
% 1.47/0.57  fof(f303,plain,(
% 1.47/0.57    ~spl5_5 | spl5_11),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f302])).
% 1.47/0.57  fof(f302,plain,(
% 1.47/0.57    $false | (~spl5_5 | spl5_11)),
% 1.47/0.57    inference(subsumption_resolution,[],[f301,f265])).
% 1.47/0.57  fof(f265,plain,(
% 1.47/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl5_5),
% 1.47/0.57    inference(forward_demodulation,[],[f252,f93])).
% 1.47/0.57  fof(f252,plain,(
% 1.47/0.57    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl5_5),
% 1.47/0.57    inference(backward_demodulation,[],[f138,f119])).
% 1.47/0.57  fof(f138,plain,(
% 1.47/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.47/0.57    inference(resolution,[],[f54,f73])).
% 1.47/0.57  fof(f301,plain,(
% 1.47/0.57    ~r1_tarski(sK3,k1_xboole_0) | (~spl5_5 | spl5_11)),
% 1.47/0.57    inference(forward_demodulation,[],[f300,f279])).
% 1.47/0.57  fof(f300,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | (~spl5_5 | spl5_11)),
% 1.47/0.57    inference(subsumption_resolution,[],[f281,f270])).
% 1.47/0.57  fof(f270,plain,(
% 1.47/0.57    k1_xboole_0 != sK3 | (~spl5_5 | spl5_11)),
% 1.47/0.57    inference(forward_demodulation,[],[f256,f93])).
% 1.47/0.57  fof(f256,plain,(
% 1.47/0.57    sK3 != k2_zfmisc_1(k1_xboole_0,sK1) | (~spl5_5 | spl5_11)),
% 1.47/0.57    inference(backward_demodulation,[],[f180,f119])).
% 1.47/0.57  fof(f180,plain,(
% 1.47/0.57    sK3 != k2_zfmisc_1(sK0,sK1) | spl5_11),
% 1.47/0.57    inference(avatar_component_clause,[],[f179])).
% 1.47/0.57  fof(f281,plain,(
% 1.47/0.57    ( ! [X0] : (k1_xboole_0 = sK3 | ~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | ~spl5_5),
% 1.47/0.57    inference(backward_demodulation,[],[f183,f279])).
% 1.47/0.57  fof(f264,plain,(
% 1.47/0.57    ~spl5_5 | spl5_6),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f263])).
% 1.47/0.57  fof(f263,plain,(
% 1.47/0.57    $false | (~spl5_5 | spl5_6)),
% 1.47/0.57    inference(subsumption_resolution,[],[f249,f58])).
% 1.47/0.57  fof(f249,plain,(
% 1.47/0.57    ~r1_tarski(k1_xboole_0,sK2) | (~spl5_5 | spl5_6)),
% 1.47/0.57    inference(backward_demodulation,[],[f125,f119])).
% 1.47/0.57  fof(f125,plain,(
% 1.47/0.57    ~r1_tarski(sK0,sK2) | spl5_6),
% 1.47/0.57    inference(avatar_component_clause,[],[f123])).
% 1.47/0.57  fof(f245,plain,(
% 1.47/0.57    spl5_14 | spl5_4),
% 1.47/0.57    inference(avatar_split_clause,[],[f139,f113,f242])).
% 1.47/0.57  fof(f139,plain,(
% 1.47/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f134,f53])).
% 1.47/0.57  fof(f134,plain,(
% 1.47/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.57    inference(resolution,[],[f54,f81])).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.47/0.57    inference(cnf_transformation,[],[f51])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(nnf_transformation,[],[f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(flattening,[],[f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.47/0.57  fof(f230,plain,(
% 1.47/0.57    spl5_2 | spl5_4),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f229])).
% 1.47/0.57  fof(f229,plain,(
% 1.47/0.57    $false | (spl5_2 | spl5_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f226,f144])).
% 1.47/0.57  fof(f144,plain,(
% 1.47/0.57    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl5_2),
% 1.47/0.57    inference(backward_demodulation,[],[f106,f142])).
% 1.47/0.57  fof(f226,plain,(
% 1.47/0.57    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl5_4),
% 1.47/0.57    inference(superposition,[],[f211,f214])).
% 1.47/0.57  fof(f214,plain,(
% 1.47/0.57    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl5_4),
% 1.47/0.57    inference(resolution,[],[f152,f55])).
% 1.47/0.57  fof(f152,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | spl5_4),
% 1.47/0.57    inference(subsumption_resolution,[],[f151,f131])).
% 1.47/0.57  fof(f151,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | spl5_4),
% 1.47/0.57    inference(superposition,[],[f61,f141])).
% 1.47/0.57  fof(f141,plain,(
% 1.47/0.57    sK0 = k1_relat_1(sK3) | spl5_4),
% 1.47/0.57    inference(backward_demodulation,[],[f132,f140])).
% 1.47/0.57  fof(f140,plain,(
% 1.47/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | spl5_4),
% 1.47/0.57    inference(subsumption_resolution,[],[f139,f115])).
% 1.47/0.57  fof(f115,plain,(
% 1.47/0.57    k1_xboole_0 != sK1 | spl5_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f113])).
% 1.47/0.57  fof(f211,plain,(
% 1.47/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f210,f184])).
% 1.47/0.57  fof(f210,plain,(
% 1.47/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f206,f199])).
% 1.47/0.57  fof(f206,plain,(
% 1.47/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.57    inference(resolution,[],[f204,f65])).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f201,plain,(
% 1.47/0.57    spl5_1),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f200])).
% 1.47/0.57  fof(f200,plain,(
% 1.47/0.57    $false | spl5_1),
% 1.47/0.57    inference(resolution,[],[f199,f143])).
% 1.47/0.57  fof(f143,plain,(
% 1.47/0.57    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl5_1),
% 1.47/0.57    inference(backward_demodulation,[],[f102,f142])).
% 1.47/0.57  fof(f102,plain,(
% 1.47/0.57    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl5_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f100])).
% 1.47/0.57  fof(f100,plain,(
% 1.47/0.57    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.47/0.57  fof(f120,plain,(
% 1.47/0.57    ~spl5_4 | spl5_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f56,f117,f113])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.47/0.57    inference(cnf_transformation,[],[f40])).
% 1.47/0.57  fof(f111,plain,(
% 1.47/0.57    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.47/0.57    inference(avatar_split_clause,[],[f57,f108,f104,f100])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.47/0.57    inference(cnf_transformation,[],[f40])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (2652)------------------------------
% 1.47/0.57  % (2652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (2652)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (2652)Memory used [KB]: 11001
% 1.47/0.57  % (2652)Time elapsed: 0.145 s
% 1.47/0.57  % (2652)------------------------------
% 1.47/0.57  % (2652)------------------------------
% 1.47/0.58  % (2638)Success in time 0.213 s
%------------------------------------------------------------------------------
