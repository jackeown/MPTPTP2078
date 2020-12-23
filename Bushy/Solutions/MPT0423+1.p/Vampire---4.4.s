%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t55_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 477 expanded)
%              Number of leaves         :   18 ( 119 expanded)
%              Depth                    :   25
%              Number of atoms          :  367 (1716 expanded)
%              Number of equality atoms :  109 ( 709 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f899,f19436])).

fof(f19436,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f19435])).

fof(f19435,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f19434,f344])).

fof(f344,plain,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f342,f119])).

fof(f119,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f112,f70])).

fof(f70,plain,(
    k1_tarski(sK0) = sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)
    & k1_tarski(sK0) = sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f53])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
        & k1_tarski(X0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)
      & k1_tarski(sK0) = sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t55_setfam_1)).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d1_tarski)).

fof(f342,plain,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ r2_hidden(sK0,sK1)
    | ~ spl6_6 ),
    inference(superposition,[],[f236,f340])).

fof(f340,plain,(
    k1_xboole_0 = k3_subset_1(sK0,sK0) ),
    inference(forward_demodulation,[],[f164,f202])).

fof(f202,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f163,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t37_xboole_1)).

fof(f163,plain,(
    r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f148,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t3_subset)).

fof(f148,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f139,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t1_subset)).

fof(f139,plain,(
    r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f116,f122])).

fof(f122,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f69,f101])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f99,f70])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t37_zfmisc_1)).

fof(f164,plain,(
    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f148,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d5_subset_1)).

fof(f236,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f194,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f69,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t4_subset)).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f19434,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f19433,f19388])).

fof(f19388,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f19387,f71])).

fof(f71,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f19387,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ spl6_4 ),
    inference(equality_resolution,[],[f19242])).

fof(f19242,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = sK4(X0,k7_setfam_1(sK0,sK1))
        | k1_tarski(X0) = k7_setfam_1(sK0,sK1) )
    | ~ spl6_4 ),
    inference(equality_factoring,[],[f19152])).

fof(f19152,plain,
    ( ! [X0] :
        ( sK4(X0,k7_setfam_1(sK0,sK1)) = X0
        | k1_xboole_0 = sK4(X0,k7_setfam_1(sK0,sK1))
        | k1_tarski(X0) = k7_setfam_1(sK0,sK1) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f19151,f340])).

fof(f19151,plain,
    ( ! [X0] :
        ( k3_subset_1(sK0,sK0) = sK4(X0,k7_setfam_1(sK0,sK1))
        | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
        | sK4(X0,k7_setfam_1(sK0,sK1)) = X0 )
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f19123])).

fof(f19123,plain,
    ( ! [X0] :
        ( k3_subset_1(sK0,sK0) = sK4(X0,k7_setfam_1(sK0,sK1))
        | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
        | sK4(X0,k7_setfam_1(sK0,sK1)) = X0
        | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
        | sK4(X0,k7_setfam_1(sK0,sK1)) = X0 )
    | ~ spl6_4 ),
    inference(superposition,[],[f1864,f2382])).

fof(f2382,plain,
    ( ! [X1] :
        ( k3_subset_1(sK0,sK4(X1,k7_setfam_1(sK0,sK1))) = sK0
        | k1_tarski(X1) = k7_setfam_1(sK0,sK1)
        | sK4(X1,k7_setfam_1(sK0,sK1)) = X1 )
    | ~ spl6_4 ),
    inference(resolution,[],[f493,f118])).

fof(f118,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK0 = X2 ) ),
    inference(superposition,[],[f113,f70])).

fof(f113,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f493,plain,
    ( ! [X9] :
        ( r2_hidden(k3_subset_1(sK0,sK4(X9,k7_setfam_1(sK0,sK1))),sK1)
        | sK4(X9,k7_setfam_1(sK0,sK1)) = X9
        | k1_tarski(X9) = k7_setfam_1(sK0,sK1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f484,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,sK1))
        | r2_hidden(k3_subset_1(sK0,X0),sK1) )
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f246,f240])).

fof(f240,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k7_setfam_1(sK0,sK1))
        | m1_subset_1(X2,k1_zfmisc_1(sK0)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f188,f107])).

fof(f188,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_4
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X0),sK1) )
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f237,f69])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X0),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl6_4 ),
    inference(resolution,[],[f188,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d8_setfam_1)).

fof(f1864,plain,
    ( ! [X4] :
        ( k3_subset_1(sK0,k3_subset_1(sK0,sK4(X4,k7_setfam_1(sK0,sK1)))) = sK4(X4,k7_setfam_1(sK0,sK1))
        | k1_tarski(X4) = k7_setfam_1(sK0,sK1)
        | sK4(X4,k7_setfam_1(sK0,sK1)) = X4 )
    | ~ spl6_4 ),
    inference(resolution,[],[f432,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',involutiveness_k3_subset_1)).

fof(f432,plain,
    ( ! [X9] :
        ( m1_subset_1(sK4(X9,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
        | sK4(X9,k7_setfam_1(sK0,sK1)) = X9
        | k1_tarski(X9) = k7_setfam_1(sK0,sK1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f240,f97])).

fof(f19433,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f19432,f71])).

fof(f19432,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ r2_hidden(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f19431])).

fof(f19431,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ r2_hidden(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(superposition,[],[f98,f19388])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f899,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f898,f193,f190])).

fof(f190,plain,
    ( spl6_5
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f898,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(forward_demodulation,[],[f897,f120])).

fof(f120,plain,(
    k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    inference(resolution,[],[f69,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',involutiveness_k7_setfam_1)).

fof(f897,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f894,f69])).

fof(f894,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f110,f120])).

fof(f235,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f233,f69])).

fof(f233,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f191,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',dt_k7_setfam_1)).

fof(f191,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f190])).
%------------------------------------------------------------------------------
