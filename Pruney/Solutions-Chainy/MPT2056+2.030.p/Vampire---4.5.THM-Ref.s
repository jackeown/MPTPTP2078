%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 289 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  393 (1362 expanded)
%              Number of equality atoms :   53 ( 226 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f766,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f433,f437,f765])).

fof(f765,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f759,f158])).

fof(f158,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f155,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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

fof(f155,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f154])).

fof(f154,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ r2_hidden(X9,k1_xboole_0) ) ),
    inference(resolution,[],[f73,f143])).

fof(f143,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f76,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f759,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_7 ),
    inference(resolution,[],[f758,f448])).

fof(f448,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK3,k1_tarski(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r1_xboole_0(sK3,k1_tarski(X0))
        | r1_xboole_0(sK3,k1_tarski(X0)) )
    | ~ spl7_7 ),
    inference(superposition,[],[f440,f139])).

fof(f139,plain,(
    ! [X4,X3] :
      ( sK5(X3,k1_tarski(X4)) = X4
      | r1_xboole_0(X3,k1_tarski(X4)) ) ),
    inference(resolution,[],[f136,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f74,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f440,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK5(sK3,X0))
        | r1_xboole_0(sK3,X0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f432,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl7_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f758,plain,(
    ~ r1_xboole_0(sK3,k1_tarski(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f757])).

fof(f757,plain,
    ( sK3 != sK3
    | ~ r1_xboole_0(sK3,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f755,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f755,plain,(
    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f754,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
        & ~ v1_xboole_0(X1) )
   => ( sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
      & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
      & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
      & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f754,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f753,f54])).

fof(f54,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f753,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f752,f55])).

fof(f55,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f752,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f751,f92])).

fof(f92,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f64,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f57,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f751,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | v1_xboole_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f750,f91])).

fof(f91,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f58,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f750,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | v1_xboole_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f746,f90])).

fof(f90,plain,(
    m1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))))) ),
    inference(definition_unfolding,[],[f59,f89,f64])).

fof(f89,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f62,f88])).

fof(f88,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f63,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f62,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f37])).

fof(f746,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | v1_xboole_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f60,f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f96,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f64,f89,f64,f64,f64])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f60,plain,(
    sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f437,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f435,f53])).

fof(f435,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f434,f54])).

fof(f434,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f429,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f67,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f429,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl7_6
  <=> v1_xboole_0(k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f433,plain,
    ( spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f425,f431,f427])).

fof(f425,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f424,f93])).

fof(f93,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f424,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))
      | v1_xboole_0(k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f423,f92])).

fof(f423,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ v1_xboole_0(X0)
      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
      | ~ v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))
      | v1_xboole_0(k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f420,f91])).

fof(f420,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ v1_xboole_0(X0)
      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
      | ~ v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))
      | v1_xboole_0(k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f359,f90])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f89,f64,f64,f64,f64])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:35:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (21048)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (21055)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (21050)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (21043)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (21059)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (21035)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21033)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (21036)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (21039)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21053)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (21032)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21057)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (21034)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21060)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21038)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (21046)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (21051)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (21049)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (21042)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (21044)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (21054)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (21056)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (21040)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21042)Refutation not found, incomplete strategy% (21042)------------------------------
% 0.21/0.55  % (21042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21042)Memory used [KB]: 10746
% 0.21/0.55  % (21042)Time elapsed: 0.149 s
% 0.21/0.55  % (21042)------------------------------
% 0.21/0.55  % (21042)------------------------------
% 0.21/0.56  % (21054)Refutation not found, incomplete strategy% (21054)------------------------------
% 0.21/0.56  % (21054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21054)Memory used [KB]: 10746
% 0.21/0.56  % (21054)Time elapsed: 0.148 s
% 0.21/0.56  % (21054)------------------------------
% 0.21/0.56  % (21054)------------------------------
% 0.21/0.56  % (21061)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (21047)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (21059)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f766,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f433,f437,f765])).
% 0.21/0.56  fof(f765,plain,(
% 0.21/0.56    ~spl7_7),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f764])).
% 0.21/0.56  fof(f764,plain,(
% 0.21/0.56    $false | ~spl7_7),
% 0.21/0.56    inference(subsumption_resolution,[],[f759,f158])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f155,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(rectify,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(condensation,[],[f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~r2_hidden(X9,k1_xboole_0)) )),
% 0.21/0.56    inference(resolution,[],[f73,f143])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f141])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f76,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.56  fof(f759,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl7_7),
% 0.21/0.56    inference(resolution,[],[f758,f448])).
% 0.21/0.56  fof(f448,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(sK3,k1_tarski(X0)) | ~v1_xboole_0(X0)) ) | ~spl7_7),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f447])).
% 0.21/0.56  fof(f447,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | r1_xboole_0(sK3,k1_tarski(X0)) | r1_xboole_0(sK3,k1_tarski(X0))) ) | ~spl7_7),
% 0.21/0.56    inference(superposition,[],[f440,f139])).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    ( ! [X4,X3] : (sK5(X3,k1_tarski(X4)) = X4 | r1_xboole_0(X3,k1_tarski(X4))) )),
% 0.21/0.56    inference(resolution,[],[f136,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f74,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.56  fof(f440,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(sK5(sK3,X0)) | r1_xboole_0(sK3,X0)) ) | ~spl7_7),
% 0.21/0.56    inference(resolution,[],[f432,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f432,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0)) ) | ~spl7_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f431])).
% 0.21/0.56  fof(f431,plain,(
% 0.21/0.56    spl7_7 <=> ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.56  fof(f758,plain,(
% 0.21/0.56    ~r1_xboole_0(sK3,k1_tarski(k1_xboole_0))),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f757])).
% 0.21/0.56  fof(f757,plain,(
% 0.21/0.56    sK3 != sK3 | ~r1_xboole_0(sK3,k1_tarski(k1_xboole_0))),
% 0.21/0.56    inference(superposition,[],[f755,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f44])).
% 0.21/0.56  fof(f755,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f754,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ~v2_struct_0(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    (sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f36,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ? [X1] : (k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) => (sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.56  fof(f754,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | v2_struct_0(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f753,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    l1_struct_0(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f753,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f752,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ~v1_xboole_0(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f752,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | v1_xboole_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f751,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 0.21/0.56    inference(definition_unfolding,[],[f57,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f751,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | ~v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | v1_xboole_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f750,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 0.21/0.56    inference(definition_unfolding,[],[f58,f64])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f750,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | ~v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | v1_xboole_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f746,f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    m1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))))),
% 0.21/0.56    inference(definition_unfolding,[],[f59,f89,f64])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f62,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f63,f64])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f746,plain,(
% 0.21/0.56    sK3 != k4_xboole_0(sK3,k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))))) | ~v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | ~v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | v1_xboole_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(superposition,[],[f60,f452])).
% 0.21/0.56  fof(f452,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f451])).
% 0.21/0.56  fof(f451,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(superposition,[],[f96,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f68,f64,f89,f64,f64,f64])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f78,f89])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    sK3 != k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    ~spl7_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f436])).
% 0.21/0.56  fof(f436,plain,(
% 0.21/0.56    $false | ~spl7_6),
% 0.21/0.56    inference(subsumption_resolution,[],[f435,f53])).
% 0.21/0.56  fof(f435,plain,(
% 0.21/0.56    v2_struct_0(sK2) | ~spl7_6),
% 0.21/0.56    inference(subsumption_resolution,[],[f434,f54])).
% 0.21/0.56  fof(f434,plain,(
% 0.21/0.56    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_6),
% 0.21/0.56    inference(resolution,[],[f429,f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.56    inference(superposition,[],[f67,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.56  fof(f429,plain,(
% 0.21/0.56    v1_xboole_0(k2_struct_0(sK2)) | ~spl7_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f427])).
% 0.21/0.56  fof(f427,plain,(
% 0.21/0.56    spl7_6 <=> v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.56  fof(f433,plain,(
% 0.21/0.56    spl7_6 | spl7_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f425,f431,f427])).
% 0.21/0.56  fof(f425,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f424,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 0.21/0.56    inference(definition_unfolding,[],[f56,f64])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f424,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0) | ~v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) | v1_xboole_0(k2_struct_0(sK2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f423,f92])).
% 0.21/0.56  fof(f423,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0) | ~v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | ~v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) | v1_xboole_0(k2_struct_0(sK2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f420,f91])).
% 0.21/0.56  fof(f420,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | ~v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) | ~v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) | v1_xboole_0(k2_struct_0(sK2))) )),
% 0.21/0.56    inference(resolution,[],[f359,f90])).
% 0.21/0.56  fof(f359,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f94,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f65,f89,f64,f64,f64,f64])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (21059)------------------------------
% 0.21/0.56  % (21059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21059)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (21059)Memory used [KB]: 6524
% 0.21/0.56  % (21059)Time elapsed: 0.138 s
% 0.21/0.56  % (21059)------------------------------
% 0.21/0.56  % (21059)------------------------------
% 0.21/0.56  % (21052)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (21041)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (21045)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (21058)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (21031)Success in time 0.217 s
%------------------------------------------------------------------------------
