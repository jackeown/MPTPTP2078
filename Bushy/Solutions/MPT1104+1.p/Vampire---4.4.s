%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t25_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:29 EDT 2019

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   55 (  97 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 449 expanded)
%              Number of equality atoms :   49 ( 160 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f193,f1125])).

fof(f1125,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f1124])).

fof(f1124,plain,
    ( $false
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f1119,f109])).

fof(f109,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f90,f76])).

fof(f76,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f65,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
                & r1_xboole_0(X1,X2)
                & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != X2
            & r1_xboole_0(sK1,X2)
            & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2
        & r1_xboole_0(X1,sK2)
        & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',t25_pre_topc)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',symmetry_r1_xboole_0)).

fof(f1119,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f1118])).

fof(f1118,plain,
    ( sK2 != sK2
    | ~ r1_xboole_0(sK2,sK1)
    | ~ spl5_15 ),
    inference(superposition,[],[f674,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',t83_xboole_1)).

fof(f674,plain,
    ( k4_xboole_0(sK2,sK1) != sK2
    | ~ spl5_15 ),
    inference(superposition,[],[f181,f306])).

fof(f306,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[],[f139,f218])).

fof(f218,plain,(
    k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f217,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f217,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f209,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f209,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f101,f75])).

fof(f75,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',redefinition_k4_subset_1)).

fof(f139,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    inference(superposition,[],[f87,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',commutativity_k2_xboole_0)).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',t40_xboole_1)).

fof(f181,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != sK2
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_15
  <=> k4_xboole_0(k2_struct_0(sK0),sK1) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f193,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f190,f72])).

fof(f72,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f190,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f178,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',dt_k2_struct_0)).

fof(f178,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_13
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f182,plain,
    ( ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f172,f180,f177])).

fof(f172,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f77,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t25_pre_topc.p',redefinition_k7_subset_1)).

fof(f77,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
