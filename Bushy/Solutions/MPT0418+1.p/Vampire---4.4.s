%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t49_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 ( 315 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f566,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f95,f143,f180,f204,f527,f563])).

fof(f563,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_7
    | ~ spl5_8
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f561,f104])).

fof(f104,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_7
  <=> ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f561,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f556,f94])).

fof(f94,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_8
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f556,plain,
    ( ~ r2_hidden(sK2,sK1)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(resolution,[],[f216,f69])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f216,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f215,f179])).

fof(f179,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl5_26
  <=> k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f215,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
        | ~ r2_hidden(X1,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f214,f203])).

fof(f203,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl5_32
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f214,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
        | ~ r2_hidden(X1,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f210,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f210,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
        | ~ r2_hidden(X1,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_26 ),
    inference(superposition,[],[f65,f179])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',d8_setfam_1)).

fof(f527,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | spl5_9
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f525,f142])).

fof(f142,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f525,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f523,f69])).

fof(f523,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r2_hidden(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(resolution,[],[f213,f91])).

fof(f91,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_6
  <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f212,f179])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f211,f203])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f209,f76])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | r2_hidden(X0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) )
    | ~ spl5_26 ),
    inference(superposition,[],[f66,f179])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f204,plain,
    ( spl5_32
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f79,f75,f202])).

fof(f79,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',dt_k7_setfam_1)).

fof(f180,plain,
    ( spl5_26
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f78,f75,f178])).

fof(f78,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',involutiveness_k7_setfam_1)).

fof(f143,plain,
    ( ~ spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f134,f90,f141])).

fof(f134,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f42,f91])).

fof(f42,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',t49_setfam_1)).

fof(f95,plain,
    ( spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f41,f93,f90])).

fof(f41,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f43,f68])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
