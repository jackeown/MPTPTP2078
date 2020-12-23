%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t63_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 158 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 451 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f123,f127,f131,f158,f257,f272,f308,f336])).

fof(f336,plain,
    ( spl7_11
    | spl7_15
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f334,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_15
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f334,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_11
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f332,f122])).

fof(f122,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_11
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f332,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | ~ spl7_44 ),
    inference(resolution,[],[f307,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',d3_xboole_0)).

fof(f307,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl7_44
  <=> sP6(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f308,plain,
    ( spl7_44
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f292,f270,f306])).

fof(f270,plain,
    ( spl7_38
  <=> r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f292,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl7_38 ),
    inference(resolution,[],[f271,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f271,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl7_38
    | ~ spl7_6
    | ~ spl7_8
    | spl7_13
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f259,f255,f156,f125,f101,f97,f270])).

fof(f97,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f101,plain,
    ( spl7_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f125,plain,
    ( spl7_13
  <=> ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f156,plain,
    ( spl7_24
  <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f255,plain,
    ( spl7_32
  <=> k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f259,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f179,f258])).

fof(f258,plain,
    ( ~ v3_setfam_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl7_13
    | ~ spl7_32 ),
    inference(superposition,[],[f126,f256])).

fof(f256,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f255])).

fof(f126,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f179,plain,
    ( v3_setfam_1(k2_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f178,f163])).

fof(f163,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f159,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',commutativity_k2_xboole_0)).

fof(f159,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(resolution,[],[f108,f102])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | k4_subset_1(k1_zfmisc_1(sK0),sK2,X1) = k2_xboole_0(sK2,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',redefinition_k4_subset_1)).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f178,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1),sK0)
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f168,f163])).

fof(f168,plain,
    ( r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1))
    | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1),sK0)
    | ~ spl7_24 ),
    inference(resolution,[],[f157,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',d13_setfam_1)).

fof(f157,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f156])).

fof(f257,plain,
    ( spl7_32
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f200,f101,f97,f255])).

fof(f200,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(resolution,[],[f116,f98])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | k4_subset_1(k1_zfmisc_1(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )
    | ~ spl7_8 ),
    inference(resolution,[],[f102,f57])).

fof(f158,plain,
    ( spl7_24
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f149,f101,f97,f156])).

fof(f149,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f102])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl7_6 ),
    inference(resolution,[],[f98,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',dt_k4_subset_1)).

fof(f131,plain,
    ( ~ spl7_15
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f119,f101,f93,f129])).

fof(f93,plain,
    ( spl7_4
  <=> v3_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f113,f94])).

fof(f94,plain,
    ( v3_setfam_1(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f113,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_setfam_1(sK1,sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f102,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f52,f125])).

fof(f52,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t63_setfam_1.p',t63_setfam_1)).

fof(f123,plain,
    ( ~ spl7_11
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f111,f97,f89,f121])).

fof(f89,plain,
    ( spl7_2
  <=> v3_setfam_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f111,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f105,f90])).

fof(f90,plain,
    ( v3_setfam_1(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ v3_setfam_1(sK2,sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f98,f66])).

fof(f103,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f53,f93])).

fof(f53,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f50,f89])).

fof(f50,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
