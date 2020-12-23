%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t51_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 251 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  336 (1024 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f318,f567,f790,f1070,f1446,f1697,f2079,f2260,f2294])).

fof(f2294,plain,(
    ~ spl6_302 ),
    inference(avatar_contradiction_clause,[],[f2289])).

fof(f2289,plain,
    ( $false
    | ~ spl6_302 ),
    inference(subsumption_resolution,[],[f62,f2268])).

fof(f2268,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_302 ),
    inference(resolution,[],[f2075,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',d3_tarski)).

fof(f2075,plain,
    ( r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl6_302 ),
    inference(avatar_component_clause,[],[f2074])).

fof(f2074,plain,
    ( spl6_302
  <=> r2_hidden(sK5(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_302])])).

fof(f62,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,sK2)
    & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(X1,sK2)
        & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',t51_setfam_1)).

fof(f2260,plain,(
    spl6_305 ),
    inference(avatar_contradiction_clause,[],[f2255])).

fof(f2255,plain,
    ( $false
    | ~ spl6_305 ),
    inference(subsumption_resolution,[],[f62,f2248])).

fof(f2248,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_305 ),
    inference(resolution,[],[f2078,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2078,plain,
    ( ~ r2_hidden(sK5(sK1,sK2),sK1)
    | ~ spl6_305 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2077,plain,
    ( spl6_305
  <=> ~ r2_hidden(sK5(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_305])])).

fof(f2079,plain,
    ( spl6_302
    | ~ spl6_305
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f2044,f1444,f2077,f2074])).

fof(f1444,plain,
    ( spl6_186
  <=> ! [X8] :
        ( r2_hidden(X8,sK2)
        | ~ r2_hidden(X8,sK1)
        | ~ m1_subset_1(X8,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f2044,plain,
    ( ~ r2_hidden(sK5(sK1,sK2),sK1)
    | r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl6_186 ),
    inference(resolution,[],[f1445,f401])).

fof(f401,plain,(
    m1_subset_1(sK5(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f137,f62])).

fof(f137,plain,(
    ! [X7] :
      ( r1_tarski(sK1,X7)
      | m1_subset_1(sK5(sK1,X7),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f93,f81])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f59,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',t4_subset)).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1445,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK2) )
    | ~ spl6_186 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1697,plain,(
    spl6_185 ),
    inference(avatar_contradiction_clause,[],[f1693])).

fof(f1693,plain,
    ( $false
    | ~ spl6_185 ),
    inference(subsumption_resolution,[],[f61,f1442])).

fof(f1442,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
    | ~ spl6_185 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1441,plain,
    ( spl6_185
  <=> ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).

fof(f61,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1446,plain,
    ( ~ spl6_185
    | spl6_186
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f1439,f160,f124,f1444,f1441])).

fof(f124,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f160,plain,
    ( spl6_20
  <=> ! [X1] :
        ( r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1439,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | ~ m1_subset_1(X8,k1_zfmisc_1(sK0))
        | ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
        | ~ r2_hidden(X8,sK1) )
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(resolution,[],[f494,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f494,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k3_subset_1(sK0,X2),X3)
        | r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ r1_tarski(X3,k7_setfam_1(sK0,sK2)) )
    | ~ spl6_20 ),
    inference(resolution,[],[f161,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(X1,sK2) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1070,plain,
    ( ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f1069,f124,f121])).

fof(f121,plain,
    ( spl6_7
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1069,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(global_subsumption,[],[f380])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(global_subsumption,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f59,f93,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(forward_demodulation,[],[f115,f91])).

fof(f91,plain,(
    k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',involutiveness_k7_setfam_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f90,f91])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK4(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK4(X0,X1,X2)),X1)
                  | r2_hidden(sK4(X0,X1,X2),X2) )
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK4(X0,X1,X2)),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK4(X0,X1,X2)),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',d8_setfam_1)).

fof(f790,plain,
    ( ~ spl6_17
    | spl6_20 ),
    inference(avatar_split_clause,[],[f789,f160,f151])).

fof(f151,plain,
    ( spl6_17
  <=> ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f789,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(global_subsumption,[],[f304])).

fof(f304,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(global_subsumption,[],[f158])).

fof(f158,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(global_subsumption,[],[f60,f157])).

fof(f157,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(forward_demodulation,[],[f146,f103])).

fof(f103,plain,(
    k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2 ),
    inference(resolution,[],[f60,f73])).

fof(f146,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(X1,k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f89,f103])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f567,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f59,f484])).

fof(f484,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_7 ),
    inference(resolution,[],[f122,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t51_setfam_1.p',dt_k7_setfam_1)).

fof(f122,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f318,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f60,f312])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_17 ),
    inference(resolution,[],[f152,f74])).

fof(f152,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f151])).
%------------------------------------------------------------------------------
