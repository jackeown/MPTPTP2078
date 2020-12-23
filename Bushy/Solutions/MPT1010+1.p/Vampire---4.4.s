%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t65_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 464 expanded)
%              Number of equality atoms :   61 (  98 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f104,f111,f120,f148,f200,f305,f497,f519,f584,f591])).

fof(f591,plain,
    ( ~ spl7_4
    | spl7_9
    | ~ spl7_78 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f586,f110])).

fof(f110,plain,
    ( k1_funct_1(sK3,sK2) != sK1
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_9
  <=> k1_funct_1(sK3,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f586,plain,
    ( k1_funct_1(sK3,sK2) = sK1
    | ~ spl7_4
    | ~ spl7_78 ),
    inference(resolution,[],[f583,f96])).

fof(f96,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f583,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK3,X0) = sK1 )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl7_78
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK3,X0) = sK1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f584,plain,
    ( spl7_78
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f577,f495,f582])).

fof(f495,plain,
    ( spl7_74
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f577,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK3,X0) = sK1 )
    | ~ spl7_74 ),
    inference(resolution,[],[f496,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',d1_tarski)).

fof(f496,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f495])).

fof(f519,plain,
    ( ~ spl7_2
    | ~ spl7_72 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f510,f89])).

fof(f89,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f510,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_72 ),
    inference(superposition,[],[f54,f493])).

fof(f493,plain,
    ( k1_tarski(sK1) = o_0_0_xboole_0
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl7_72
  <=> k1_tarski(sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',fc2_xboole_0)).

fof(f497,plain,
    ( spl7_72
    | spl7_74
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f308,f303,f146,f102,f495,f492])).

fof(f102,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f146,plain,
    ( spl7_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f303,plain,
    ( spl7_46
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(sK3,X2,X1)
        | o_0_0_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | k1_tarski(sK1) = o_0_0_xboole_0 )
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f307,f103])).

fof(f103,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | k1_tarski(sK1) = o_0_0_xboole_0 )
    | ~ spl7_18
    | ~ spl7_46 ),
    inference(resolution,[],[f304,f147])).

fof(f147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f304,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r2_hidden(X0,X2)
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ v1_funct_2(sK3,X2,X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl7_46
    | ~ spl7_0
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f205,f198,f81,f303])).

fof(f81,plain,
    ( spl7_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f198,plain,
    ( spl7_26
  <=> ! [X1,X3,X0,X2] :
        ( o_0_0_xboole_0 = X1
        | r2_hidden(k1_funct_1(X3,X2),X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ v1_funct_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(sK3,X2,X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl7_0
    | ~ spl7_26 ),
    inference(resolution,[],[f199,f82])).

fof(f82,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f199,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | r2_hidden(k1_funct_1(X3,X2),X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl7_26
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f196,f118,f198])).

fof(f118,plain,
    ( spl7_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] :
        ( o_0_0_xboole_0 = X1
        | r2_hidden(k1_funct_1(X3,X2),X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ v1_funct_1(X3) )
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f71,f119])).

fof(f119,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',t7_funct_2)).

fof(f148,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f50,f146])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k1_funct_1(sK3,sK2) != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK3,sK2) != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',t65_funct_2)).

fof(f120,plain,
    ( spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f112,f88,f118])).

fof(f112,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_2 ),
    inference(resolution,[],[f55,f89])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',t6_boole)).

fof(f111,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    k1_funct_1(sK3,sK2) != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f53,f88])).

fof(f53,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t65_funct_2.p',dt_o_0_0_xboole_0)).

fof(f83,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f48,f81])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
