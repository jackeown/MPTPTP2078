%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t63_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 550 expanded)
%              Number of leaves         :   37 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  539 (1556 expanded)
%              Number of equality atoms :  195 ( 667 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f199,f203,f321,f344,f1115,f1118,f1536,f1539,f1633,f1652,f2003,f2053,f2092,f2149,f2310])).

fof(f2310,plain,
    ( ~ spl6_18
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f2309])).

fof(f2309,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f2308,f66])).

fof(f66,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',dt_o_0_0_xboole_0)).

fof(f2308,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_18
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f2307,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f93,f67,f88,f67])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t54_mcart_1)).

fof(f67,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',d2_xboole_0)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t55_mcart_1)).

fof(f2307,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,o_0_0_xboole_0))
    | ~ spl6_18
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f378,f963])).

fof(f963,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl6_40
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f378,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_18 ),
    inference(resolution,[],[f320,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t7_boole)).

fof(f320,plain,
    ( r2_hidden(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_18
  <=> r2_hidden(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f2149,plain,
    ( spl6_13
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f2148])).

fof(f2148,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f2104,f123])).

fof(f123,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2,X3) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f90,f67,f88,f67])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2104,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0),sK1,sK2)
    | ~ spl6_13
    | ~ spl6_40 ),
    inference(backward_demodulation,[],[f963,f292])).

fof(f292,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_13
  <=> o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f2092,plain,
    ( ~ spl6_0
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f2091])).

fof(f2091,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f2086,f100])).

fof(f100,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f65,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
      | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
      | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
      | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f55])).

fof(f55,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) )
   => ( k1_xboole_0 != sK0
      & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
        | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
        | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
        | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
        | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
        | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
        | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
            & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
            & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
            & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t63_mcart_1)).

fof(f2086,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_0
    | ~ spl6_16 ),
    inference(resolution,[],[f353,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,o_0_0_xboole_0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f67,f67])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t3_xboole_1)).

fof(f353,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f314,f129])).

fof(f129,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_0
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f314,plain,
    ( o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl6_16
  <=> o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f2053,plain,
    ( ~ spl6_6
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f2052])).

fof(f2052,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2051,f100])).

fof(f2051,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2040,f589])).

fof(f589,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f587,f100])).

fof(f587,plain,
    ( o_0_0_xboole_0 = sK0
    | m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_6 ),
    inference(resolution,[],[f147,f283])).

fof(f283,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | o_0_0_xboole_0 = X1
      | m1_subset_1(sK4(X1),X2) ) ),
    inference(resolution,[],[f228,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t3_subset)).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0),X1)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f70,f67])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t34_mcart_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t4_subset)).

fof(f147,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_6
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2040,plain,
    ( ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | o_0_0_xboole_0 = sK0
    | ~ spl6_46 ),
    inference(resolution,[],[f769,f1978])).

fof(f1978,plain,
    ( ~ r2_hidden(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),sK0)
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f1977,f100])).

fof(f1977,plain,
    ( ~ r2_hidden(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),sK0)
    | o_0_0_xboole_0 = sK0
    | ~ spl6_46 ),
    inference(equality_resolution,[],[f1972])).

fof(f1972,plain,
    ( ! [X5] :
        ( sK4(sK0) != sK4(X5)
        | ~ r2_hidden(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),X5)
        | o_0_0_xboole_0 = X5 )
    | ~ spl6_46 ),
    inference(superposition,[],[f104,f981])).

fof(f981,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f980])).

fof(f980,plain,
    ( spl6_46
  <=> k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f99,f67])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f87,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',d3_mcart_1)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',d4_mcart_1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f769,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k9_mcart_1(X1,X2,X3,X4,X0),X2)
      | ~ m1_subset_1(X0,k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))
      | o_0_0_xboole_0 = X2 ) ),
    inference(resolution,[],[f119,f185])).

fof(f185,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | o_0_0_xboole_0 = X4 ) ),
    inference(resolution,[],[f76,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t6_boole)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t2_subset)).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f98,f88])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',dt_k9_mcart_1)).

fof(f2003,plain,
    ( ~ spl6_18
    | ~ spl6_50 ),
    inference(avatar_contradiction_clause,[],[f2002])).

fof(f2002,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f2001,f320])).

fof(f2001,plain,
    ( ~ r2_hidden(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_50 ),
    inference(resolution,[],[f2000,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t1_subset)).

fof(f2000,plain,
    ( ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f1999,f100])).

fof(f1999,plain,
    ( ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | ~ spl6_50 ),
    inference(resolution,[],[f1986,f649])).

fof(f649,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X0),X1)
      | ~ m1_subset_1(X0,k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))
      | o_0_0_xboole_0 = X1 ) ),
    inference(resolution,[],[f118,f185])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f97,f88])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',dt_k8_mcart_1)).

fof(f1986,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),sK0)
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f1985,f100])).

fof(f1985,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),sK0)
    | o_0_0_xboole_0 = sK0
    | ~ spl6_50 ),
    inference(equality_resolution,[],[f1981])).

fof(f1981,plain,
    ( ! [X4] :
        ( sK4(sK0) != sK4(X4)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_50 ),
    inference(superposition,[],[f105,f1500])).

fof(f1500,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1499,plain,
    ( spl6_50
  <=> k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f99,f67])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1652,plain,
    ( spl6_50
    | spl6_40
    | ~ spl6_18
    | spl6_43
    | spl6_45 ),
    inference(avatar_split_clause,[],[f1651,f971,f965,f319,f962,f1499])).

fof(f965,plain,
    ( spl6_43
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f971,plain,
    ( spl6_45
  <=> o_0_0_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1651,plain,
    ( o_0_0_xboole_0 = sK3
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0)
    | ~ spl6_18
    | ~ spl6_43
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1650,f100])).

fof(f1650,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK0
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0)
    | ~ spl6_18
    | ~ spl6_43
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1649,f966])).

fof(f966,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f965])).

fof(f1649,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0)
    | ~ spl6_18
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1644,f972])).

fof(f972,plain,
    ( o_0_0_xboole_0 != sK2
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f971])).

fof(f1644,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) = sK4(sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f320,f945])).

fof(f945,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(resolution,[],[f115,f75])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f94,f99,f88,f67,f67,f67,f67])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t60_mcart_1)).

fof(f1633,plain,
    ( spl6_40
    | spl6_46
    | ~ spl6_6
    | spl6_43
    | spl6_45 ),
    inference(avatar_split_clause,[],[f1632,f971,f965,f146,f980,f962])).

fof(f1632,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0)
    | o_0_0_xboole_0 = sK3
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1631,f100])).

fof(f1631,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0)
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK3
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1630,f966])).

fof(f1630,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK3
    | ~ spl6_6
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1628,f972])).

fof(f1628,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) = sK4(sK0)
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK3
    | ~ spl6_6 ),
    inference(resolution,[],[f589,f115])).

fof(f1539,plain,
    ( spl6_17
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f1538])).

fof(f1538,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f1512,f122])).

fof(f122,plain,(
    ! [X2,X0,X3] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,o_0_0_xboole_0),X2,X3) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f91,f67,f88,f67])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1512,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2,sK3)
    | ~ spl6_17
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f969,f311])).

fof(f311,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl6_17
  <=> o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f969,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl6_42
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f1536,plain,
    ( spl6_13
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f1535])).

fof(f1535,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f1510,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),o_0_0_xboole_0,X3) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f92,f67,f88,f67])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1510,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),o_0_0_xboole_0,sK2)
    | ~ spl6_13
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f969,f292])).

fof(f1118,plain,
    ( spl6_17
    | ~ spl6_44 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f1001,f121])).

fof(f1001,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0,sK3)
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f975,f311])).

fof(f975,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f974])).

fof(f974,plain,
    ( spl6_44
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f1115,plain,
    ( spl6_13
    | ~ spl6_44 ),
    inference(avatar_contradiction_clause,[],[f1114])).

fof(f1114,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f999,f120])).

fof(f999,plain,
    ( o_0_0_xboole_0 != k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,o_0_0_xboole_0)
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f975,f292])).

fof(f344,plain,
    ( ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f341,f100])).

fof(f341,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(resolution,[],[f325,f103])).

fof(f325,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f295,f147])).

fof(f295,plain,
    ( o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl6_12
  <=> o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f321,plain,
    ( spl6_16
    | spl6_18
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f308,f128,f319,f313])).

fof(f308,plain,
    ( r2_hidden(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)
    | ~ spl6_0 ),
    inference(resolution,[],[f304,f185])).

fof(f304,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f303,f100])).

fof(f303,plain,
    ( o_0_0_xboole_0 = sK0
    | m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_0 ),
    inference(resolution,[],[f129,f283])).

fof(f203,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f201,f100])).

fof(f201,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_4 ),
    inference(resolution,[],[f141,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f85,f67])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t63_mcart_1.p',t49_mcart_1)).

fof(f141,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_4
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f199,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f192,f100])).

fof(f192,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(resolution,[],[f108,f135])).

fof(f135,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_2
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f67])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f148,plain,
    ( spl6_0
    | spl6_2
    | spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f101,f146,f140,f134,f128])).

fof(f101,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    inference(definition_unfolding,[],[f64,f88,f88,f88,f88])).

fof(f64,plain,
    ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
    | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
    | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
    | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
