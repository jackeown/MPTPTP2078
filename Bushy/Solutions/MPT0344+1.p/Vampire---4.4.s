%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t10_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 167 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f74,f78,f85,f90])).

fof(f90,plain,
    ( spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t10_subset_1.p',t6_boole)).

fof(f54,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f85,plain,
    ( spl4_13
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f83,f73])).

fof(f73,plain,
    ( ~ m1_subset_1(sK2(sK1),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_13
  <=> ~ m1_subset_1(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f83,plain,
    ( m1_subset_1(sK2(sK1),sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f80,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f77,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t10_subset_1.p',d1_xboole_0)).

fof(f77,plain,
    ( r2_hidden(sK2(sK1),sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_14
  <=> r2_hidden(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f80,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK2(sK1),sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t10_subset_1.p',d2_subset_1)).

fof(f78,plain,
    ( spl4_6
    | spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f43,f76,f53])).

fof(f43,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( r2_hidden(sK2(sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t10_subset_1.p',l3_subset_1)).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f74,plain,
    ( spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f57,f72,f53])).

fof(f57,plain,
    ( ~ m1_subset_1(sK2(sK1),sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f23,f32])).

fof(f23,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t10_subset_1.p',t10_subset_1)).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
