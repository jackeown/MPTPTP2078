%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t28_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 671 expanded)
%              Number of leaves         :   57 ( 267 expanded)
%              Depth                    :   15
%              Number of atoms          :  681 (4525 expanded)
%              Number of equality atoms :   33 ( 325 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f106,f113,f120,f127,f134,f141,f148,f157,f164,f174,f184,f195,f203,f213,f233,f245,f252,f264,f271,f287,f303,f314,f340,f348,f357,f367,f375,f392,f406,f418,f433,f443,f445,f447,f449,f451,f453,f458])).

fof(f458,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f456,f251])).

fof(f251,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_34
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f456,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f455,f263])).

fof(f263,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_36
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f455,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f454,f167])).

fof(f167,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f119,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t7_boole)).

fof(f119,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f454,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f440,f286])).

fof(f286,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl6_40
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f440,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_32 ),
    inference(resolution,[],[f88,f244])).

fof(f244,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl6_32
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f88,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t28_connsp_2)).

fof(f68,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f453,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f434,f251])).

fof(f434,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f244,f263,f167,f286,f88])).

fof(f451,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f435,f286])).

fof(f435,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f244,f263,f167,f251,f88])).

fof(f449,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f436,f167])).

fof(f436,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f244,f263,f286,f251,f88])).

fof(f447,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f437,f263])).

fof(f437,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f244,f167,f286,f251,f88])).

fof(f445,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f438,f244])).

fof(f438,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f263,f167,f286,f251,f88])).

fof(f443,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f244,f263,f167,f286,f251,f88])).

fof(f433,plain,
    ( ~ spl6_65
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f419,f416,f118,f431])).

fof(f431,plain,
    ( spl6_65
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f416,plain,
    ( spl6_62
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f419,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f119,f417,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t5_subset)).

fof(f417,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f416])).

fof(f418,plain,
    ( spl6_62
    | spl6_61 ),
    inference(avatar_split_clause,[],[f407,f401,f416])).

fof(f401,plain,
    ( spl6_61
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f407,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_61 ),
    inference(unit_resulting_resolution,[],[f78,f402,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t2_subset)).

fof(f402,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f401])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',existence_m1_subset_1)).

fof(f406,plain,
    ( ~ spl6_59
    | spl6_60
    | spl6_43 ),
    inference(avatar_split_clause,[],[f304,f301,f404,f398])).

fof(f398,plain,
    ( spl6_59
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f404,plain,
    ( spl6_60
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f301,plain,
    ( spl6_43
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f304,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl6_43 ),
    inference(resolution,[],[f302,f81])).

fof(f302,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f301])).

fof(f392,plain,
    ( ~ spl6_57
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f381,f373,f390])).

fof(f390,plain,
    ( spl6_57
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f373,plain,
    ( spl6_54
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f381,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f374,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',antisymmetry_r2_hidden)).

fof(f374,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f373])).

fof(f375,plain,
    ( spl6_54
    | spl6_25 ),
    inference(avatar_split_clause,[],[f273,f193,f373])).

fof(f193,plain,
    ( spl6_25
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f273,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f78,f194,f81])).

fof(f194,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f193])).

fof(f367,plain,
    ( ~ spl6_53
    | spl6_51 ),
    inference(avatar_split_clause,[],[f359,f355,f365])).

fof(f365,plain,
    ( spl6_53
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f355,plain,
    ( spl6_51
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f359,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f356,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t1_subset)).

fof(f356,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f355])).

fof(f357,plain,
    ( ~ spl6_51
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f288,f285,f118,f355])).

fof(f288,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f119,f286,f85])).

fof(f348,plain,
    ( spl6_48
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f341,f338,f346])).

fof(f346,plain,
    ( spl6_48
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f338,plain,
    ( spl6_46
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f341,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_46 ),
    inference(superposition,[],[f78,f339])).

fof(f339,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl6_46
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f322,f312,f338])).

fof(f312,plain,
    ( spl6_44
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f322,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f313,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',t6_boole)).

fof(f313,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( spl6_44
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f305,f118,f312])).

fof(f305,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f78,f279,f81])).

fof(f279,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f119,f78,f85])).

fof(f303,plain,
    ( ~ spl6_43
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f292,f285,f301])).

fof(f292,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f286,f79])).

fof(f287,plain,
    ( spl6_40
    | ~ spl6_14
    | spl6_25 ),
    inference(avatar_split_clause,[],[f272,f193,f146,f285])).

fof(f146,plain,
    ( spl6_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f272,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f147,f194,f81])).

fof(f147,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f271,plain,
    ( spl6_38
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f224,f211,f162,f269])).

fof(f269,plain,
    ( spl6_38
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f162,plain,
    ( spl6_18
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f211,plain,
    ( spl6_28
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f224,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f218,f212])).

fof(f212,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f211])).

fof(f218,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f163,f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',dt_k2_struct_0)).

fof(f163,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f264,plain,
    ( spl6_36
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f255,f201,f111,f104,f262])).

fof(f104,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f111,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f201,plain,
    ( spl6_26
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f255,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f253,f202])).

fof(f202,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f201])).

fof(f253,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f105,f112,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',fc10_tops_1)).

fof(f112,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f105,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f252,plain,
    ( spl6_34
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f225,f201,f155,f250])).

fof(f155,plain,
    ( spl6_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f225,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f217,f202])).

fof(f217,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f156,f73])).

fof(f156,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f245,plain,
    ( spl6_32
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f236,f201,f111,f104,f243])).

fof(f236,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f234,f202])).

fof(f234,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f105,f112,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',fc4_pre_topc)).

fof(f233,plain,
    ( spl6_30
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f226,f182,f125,f231])).

fof(f231,plain,
    ( spl6_30
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f125,plain,
    ( spl6_8
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f182,plain,
    ( spl6_22
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f226,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f216,f183])).

fof(f183,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f216,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f126,f73])).

fof(f126,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f213,plain,
    ( spl6_28
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f177,f162,f211])).

fof(f177,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f163,f72])).

fof(f72,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',d3_struct_0)).

fof(f203,plain,
    ( spl6_26
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f176,f155,f201])).

fof(f176,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f156,f72])).

fof(f195,plain,
    ( ~ spl6_25
    | spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f188,f155,f97,f193])).

fof(f97,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f188,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f185,f176])).

fof(f185,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f98,f156,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',fc5_struct_0)).

fof(f98,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f184,plain,
    ( spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f175,f125,f182])).

fof(f175,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f126,f72])).

fof(f174,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f92,f172])).

fof(f172,plain,
    ( spl6_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f92,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f64,f69])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f164,plain,
    ( spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f150,f132,f162])).

fof(f132,plain,
    ( spl6_10
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f150,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f133,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',dt_l1_pre_topc)).

fof(f133,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f157,plain,
    ( spl6_16
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f149,f111,f155])).

fof(f149,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f112,f71])).

fof(f148,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f63,f146])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f141,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f69,f139])).

fof(f139,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f134,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f87,f132])).

fof(f87,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f58])).

fof(f58,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',existence_l1_pre_topc)).

fof(f127,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f86,f125])).

fof(f86,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f56])).

fof(f56,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',existence_l1_struct_0)).

fof(f120,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f70,f118])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t28_connsp_2.p',fc1_xboole_0)).

fof(f113,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f62,f111])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f61,f104])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f60,f97])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
