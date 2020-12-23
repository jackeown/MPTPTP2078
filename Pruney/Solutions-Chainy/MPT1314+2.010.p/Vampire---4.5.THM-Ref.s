%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:45 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 315 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  526 (1526 expanded)
%              Number of equality atoms :   76 ( 251 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f163,f199,f210,f305,f308,f360,f475,f527,f592,f596,f600])).

fof(f600,plain,(
    ~ spl9_47 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl9_47 ),
    inference(resolution,[],[f591,f58])).

fof(f58,plain,(
    ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v3_pre_topc(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK1)
              & m1_pre_topc(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK1)
            & m1_pre_topc(X2,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK2,sK1)
          & m1_pre_topc(X2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK2,sK1)
        & m1_pre_topc(X2,sK1) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK3)
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & v3_pre_topc(sK2,sK1)
      & m1_pre_topc(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK3)
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ~ v3_pre_topc(sK4,sK3)
      & sK2 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f591,plain,
    ( v3_pre_topc(sK4,sK3)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl9_47
  <=> v3_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f596,plain,
    ( ~ spl9_7
    | ~ spl9_9
    | spl9_37 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_9
    | spl9_37 ),
    inference(resolution,[],[f593,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f593,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_7
    | ~ spl9_9
    | spl9_37 ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_7
    | ~ spl9_9
    | spl9_37 ),
    inference(superposition,[],[f526,f345])).

fof(f345,plain,
    ( ! [X2] :
        ( k1_setfam_1(k2_tarski(X2,k2_struct_0(sK3))) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,
    ( ! [X2] :
        ( k1_setfam_1(k2_tarski(X2,k2_struct_0(sK3))) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(superposition,[],[f209,f328])).

fof(f328,plain,
    ( ! [X4] :
        ( k2_struct_0(k1_pre_topc(sK3,X4)) = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl9_7 ),
    inference(resolution,[],[f325,f189])).

fof(f189,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_7
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f319,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f318])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f96,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f209,plain,
    ( ! [X0] :
        ( k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_9
  <=> ! [X0] :
        ( k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f526,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_37 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl9_37
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f592,plain,
    ( ~ spl9_3
    | spl9_47
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f577,f520,f208,f188,f589,f153])).

fof(f153,plain,
    ( spl9_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f520,plain,
    ( spl9_36
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f577,plain,
    ( v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(superposition,[],[f522,f345])).

fof(f522,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f520])).

fof(f527,plain,
    ( spl9_36
    | ~ spl9_37
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f518,f473,f298,f524,f520])).

fof(f298,plain,
    ( spl9_16
  <=> ! [X1] : k1_setfam_1(k2_tarski(X1,k2_struct_0(sK3))) = k9_subset_1(u1_struct_0(sK3),X1,k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f473,plain,
    ( spl9_30
  <=> ! [X0] :
        ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f518,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3)
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f517,f299])).

fof(f299,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(X1,k2_struct_0(sK3))) = k9_subset_1(u1_struct_0(sK3),X1,k2_struct_0(sK3))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f298])).

fof(f517,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f515,f299])).

fof(f515,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_30 ),
    inference(resolution,[],[f474,f54])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( ~ spl9_1
    | ~ spl9_18
    | spl9_30 ),
    inference(avatar_split_clause,[],[f469,f473,f351,f111])).

fof(f111,plain,
    ( spl9_1
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f351,plain,
    ( spl9_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f469,plain,(
    ! [X0] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f94,f88])).

fof(f88,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK8(X0,X1,X2),X0)
                    & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK8(X0,X1,X2),X0)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

fof(f360,plain,(
    spl9_18 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl9_18 ),
    inference(resolution,[],[f353,f89])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f353,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_18 ),
    inference(avatar_component_clause,[],[f351])).

fof(f308,plain,(
    spl9_15 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl9_15 ),
    inference(resolution,[],[f296,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f296,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl9_15
  <=> m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f305,plain,
    ( ~ spl9_15
    | spl9_16
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f291,f188,f298,f294])).

fof(f291,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3)))
        | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl9_7 ),
    inference(superposition,[],[f91,f244])).

fof(f244,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = k9_subset_1(k2_struct_0(sK3),X4,k2_struct_0(sK3))
    | ~ spl9_7 ),
    inference(resolution,[],[f241,f189])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X0)) ) ),
    inference(resolution,[],[f230,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f230,plain,(
    ! [X4,X5] :
      ( ~ l1_struct_0(X4)
      | k9_subset_1(u1_struct_0(X4),X5,k2_struct_0(X4)) = k9_subset_1(k2_struct_0(X4),X5,k2_struct_0(X4)) ) ),
    inference(resolution,[],[f139,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f139,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k9_subset_1(X24,X23,X24) ) ),
    inference(resolution,[],[f99,f97])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | k9_subset_1(X2,X0,X1) = k9_subset_1(X3,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f91,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f87,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f210,plain,
    ( ~ spl9_7
    | spl9_9
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f206,f188,f208,f188])).

fof(f206,plain,
    ( ! [X0] :
        ( k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3) )
    | ~ spl9_7 ),
    inference(resolution,[],[f204,f86])).

fof(f204,plain,
    ( ! [X9] :
        ( ~ m1_pre_topc(X9,sK3)
        | k2_struct_0(X9) = k1_setfam_1(k2_tarski(k2_struct_0(X9),k2_struct_0(sK3))) )
    | ~ spl9_7 ),
    inference(resolution,[],[f189,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(condensation,[],[f101])).

fof(f101,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | k2_struct_0(X1) = k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X2)))
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) ) ),
    inference(resolution,[],[f71,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f84,f83])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ~ sP0(sK7(X0,X1),X1,X0)
                & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X3] :
                    ( sP0(X3,X1,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ sP0(sK7(X0,X1),X1,X0)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X3] :
                    ( sP0(X3,X1,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( sP0(X2,X1,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( sP0(X2,X1,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( sP0(X2,X1,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> ? [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
            & r2_hidden(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f199,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl9_7 ),
    inference(resolution,[],[f196,f52])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_7 ),
    inference(resolution,[],[f195,f54])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_7 ),
    inference(resolution,[],[f190,f75])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f163,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl9_3 ),
    inference(resolution,[],[f155,f56])).

fof(f155,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f120,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f113,f52])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (4512)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (4509)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (4520)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (4528)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (4521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (4529)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.57  % (4513)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.57  % (4528)Refutation not found, incomplete strategy% (4528)------------------------------
% 1.46/0.57  % (4528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (4528)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (4528)Memory used [KB]: 10746
% 1.46/0.58  % (4528)Time elapsed: 0.140 s
% 1.46/0.58  % (4528)------------------------------
% 1.46/0.58  % (4528)------------------------------
% 1.46/0.58  % (4525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.59  % (4533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.59  % (4517)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.60  % (4507)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.60  % (4508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.69/0.60  % (4510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.69/0.60  % (4506)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.69/0.60  % (4508)Refutation not found, incomplete strategy% (4508)------------------------------
% 1.69/0.60  % (4508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (4508)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.60  
% 1.69/0.60  % (4508)Memory used [KB]: 10746
% 1.69/0.60  % (4508)Time elapsed: 0.168 s
% 1.69/0.60  % (4508)------------------------------
% 1.69/0.60  % (4508)------------------------------
% 1.69/0.61  % (4526)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.61  % (4532)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.61  % (4531)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.61  % (4530)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.69/0.61  % (4534)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.61  % (4524)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.69/0.61  % (4523)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.61  % (4522)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.69/0.62  % (4523)Refutation not found, incomplete strategy% (4523)------------------------------
% 1.69/0.62  % (4523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (4523)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (4523)Memory used [KB]: 10618
% 1.69/0.62  % (4523)Time elapsed: 0.181 s
% 1.69/0.62  % (4523)------------------------------
% 1.69/0.62  % (4523)------------------------------
% 1.69/0.62  % (4516)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.69/0.62  % (4518)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.62  % (4515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.69/0.62  % (4511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.62  % (4514)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.69/0.62  % (4527)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.63  % (4516)Refutation not found, incomplete strategy% (4516)------------------------------
% 1.69/0.63  % (4516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (4516)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (4516)Memory used [KB]: 10746
% 1.69/0.63  % (4516)Time elapsed: 0.193 s
% 1.69/0.63  % (4516)------------------------------
% 1.69/0.63  % (4516)------------------------------
% 1.69/0.63  % (4519)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.69/0.64  % (4535)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.65  % (4515)Refutation not found, incomplete strategy% (4515)------------------------------
% 1.69/0.65  % (4515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.65  % (4515)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.65  
% 1.69/0.65  % (4515)Memory used [KB]: 10746
% 1.69/0.65  % (4515)Time elapsed: 0.199 s
% 1.69/0.65  % (4515)------------------------------
% 1.69/0.65  % (4515)------------------------------
% 1.69/0.65  % (4514)Refutation not found, incomplete strategy% (4514)------------------------------
% 1.69/0.65  % (4514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.65  % (4514)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.65  
% 1.69/0.65  % (4514)Memory used [KB]: 10874
% 1.69/0.65  % (4514)Time elapsed: 0.221 s
% 1.69/0.65  % (4514)------------------------------
% 1.69/0.65  % (4514)------------------------------
% 2.25/0.70  % (4518)Refutation found. Thanks to Tanya!
% 2.25/0.70  % SZS status Theorem for theBenchmark
% 2.25/0.70  % SZS output start Proof for theBenchmark
% 2.25/0.70  fof(f602,plain,(
% 2.25/0.70    $false),
% 2.25/0.70    inference(avatar_sat_refutation,[],[f120,f163,f199,f210,f305,f308,f360,f475,f527,f592,f596,f600])).
% 2.25/0.70  fof(f600,plain,(
% 2.25/0.70    ~spl9_47),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f597])).
% 2.25/0.70  fof(f597,plain,(
% 2.25/0.70    $false | ~spl9_47),
% 2.25/0.70    inference(resolution,[],[f591,f58])).
% 2.25/0.70  fof(f58,plain,(
% 2.25/0.70    ~v3_pre_topc(sK4,sK3)),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f36,plain,(
% 2.25/0.70    (((~v3_pre_topc(sK4,sK3) & sK2 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 2.25/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f35,f34,f33,f32])).
% 2.25/0.70  fof(f32,plain,(
% 2.25/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f33,plain,(
% 2.25/0.70    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f34,plain,(
% 2.25/0.70    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(X2,sK1)) => (? [X3] : (~v3_pre_topc(X3,sK3) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(sK3,sK1))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f35,plain,(
% 2.25/0.70    ? [X3] : (~v3_pre_topc(X3,sK3) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) => (~v3_pre_topc(sK4,sK3) & sK2 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f17,plain,(
% 2.25/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.25/0.70    inference(flattening,[],[f16])).
% 2.25/0.70  fof(f16,plain,(
% 2.25/0.70    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f15])).
% 2.25/0.70  fof(f15,negated_conjecture,(
% 2.25/0.70    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.25/0.70    inference(negated_conjecture,[],[f14])).
% 2.25/0.70  fof(f14,conjecture,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 2.25/0.70  fof(f591,plain,(
% 2.25/0.70    v3_pre_topc(sK4,sK3) | ~spl9_47),
% 2.25/0.70    inference(avatar_component_clause,[],[f589])).
% 2.25/0.70  fof(f589,plain,(
% 2.25/0.70    spl9_47 <=> v3_pre_topc(sK4,sK3)),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 2.25/0.70  fof(f596,plain,(
% 2.25/0.70    ~spl9_7 | ~spl9_9 | spl9_37),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f594])).
% 2.25/0.70  fof(f594,plain,(
% 2.25/0.70    $false | (~spl9_7 | ~spl9_9 | spl9_37)),
% 2.25/0.70    inference(resolution,[],[f593,f56])).
% 2.25/0.70  fof(f56,plain,(
% 2.25/0.70    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f593,plain,(
% 2.25/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | (~spl9_7 | ~spl9_9 | spl9_37)),
% 2.25/0.70    inference(duplicate_literal_removal,[],[f568])).
% 2.25/0.70  fof(f568,plain,(
% 2.25/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | (~spl9_7 | ~spl9_9 | spl9_37)),
% 2.25/0.70    inference(superposition,[],[f526,f345])).
% 2.25/0.70  fof(f345,plain,(
% 2.25/0.70    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,k2_struct_0(sK3))) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (~spl9_7 | ~spl9_9)),
% 2.25/0.70    inference(duplicate_literal_removal,[],[f339])).
% 2.25/0.70  fof(f339,plain,(
% 2.25/0.70    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,k2_struct_0(sK3))) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (~spl9_7 | ~spl9_9)),
% 2.25/0.70    inference(superposition,[],[f209,f328])).
% 2.25/0.70  fof(f328,plain,(
% 2.25/0.70    ( ! [X4] : (k2_struct_0(k1_pre_topc(sK3,X4)) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl9_7),
% 2.25/0.70    inference(resolution,[],[f325,f189])).
% 2.25/0.70  fof(f189,plain,(
% 2.25/0.70    l1_pre_topc(sK3) | ~spl9_7),
% 2.25/0.70    inference(avatar_component_clause,[],[f188])).
% 2.25/0.70  fof(f188,plain,(
% 2.25/0.70    spl9_7 <=> l1_pre_topc(sK3)),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 2.25/0.70  fof(f325,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 2.25/0.70    inference(duplicate_literal_removal,[],[f324])).
% 2.25/0.70  fof(f324,plain,(
% 2.25/0.70    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(resolution,[],[f319,f86])).
% 2.25/0.70  fof(f86,plain,(
% 2.25/0.70    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f28])).
% 2.25/0.70  fof(f28,plain,(
% 2.25/0.70    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(flattening,[],[f27])).
% 2.25/0.70  fof(f27,plain,(
% 2.25/0.70    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.25/0.70    inference(ennf_transformation,[],[f8])).
% 2.25/0.70  fof(f8,axiom,(
% 2.25/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 2.25/0.70  fof(f319,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(duplicate_literal_removal,[],[f318])).
% 2.25/0.70  fof(f318,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(resolution,[],[f96,f85])).
% 2.25/0.70  fof(f85,plain,(
% 2.25/0.70    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f28])).
% 2.25/0.70  fof(f96,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(equality_resolution,[],[f81])).
% 2.25/0.70  fof(f81,plain,(
% 2.25/0.70    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f51])).
% 2.25/0.70  fof(f51,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(nnf_transformation,[],[f25])).
% 2.25/0.70  fof(f25,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(flattening,[],[f24])).
% 2.25/0.70  fof(f24,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f6])).
% 2.25/0.70  fof(f6,axiom,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 2.25/0.70  fof(f209,plain,(
% 2.25/0.70    ( ! [X0] : (k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl9_9),
% 2.25/0.70    inference(avatar_component_clause,[],[f208])).
% 2.25/0.70  fof(f208,plain,(
% 2.25/0.70    spl9_9 <=> ! [X0] : (k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 2.25/0.70  fof(f526,plain,(
% 2.25/0.70    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | spl9_37),
% 2.25/0.70    inference(avatar_component_clause,[],[f524])).
% 2.25/0.70  fof(f524,plain,(
% 2.25/0.70    spl9_37 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 2.25/0.70  fof(f592,plain,(
% 2.25/0.70    ~spl9_3 | spl9_47 | ~spl9_7 | ~spl9_9 | ~spl9_36),
% 2.25/0.70    inference(avatar_split_clause,[],[f577,f520,f208,f188,f589,f153])).
% 2.25/0.70  fof(f153,plain,(
% 2.25/0.70    spl9_3 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.25/0.70  fof(f520,plain,(
% 2.25/0.70    spl9_36 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3)),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 2.25/0.70  fof(f577,plain,(
% 2.25/0.70    v3_pre_topc(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | (~spl9_7 | ~spl9_9 | ~spl9_36)),
% 2.25/0.70    inference(superposition,[],[f522,f345])).
% 2.25/0.70  fof(f522,plain,(
% 2.25/0.70    v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3) | ~spl9_36),
% 2.25/0.70    inference(avatar_component_clause,[],[f520])).
% 2.25/0.70  fof(f527,plain,(
% 2.25/0.70    spl9_36 | ~spl9_37 | ~spl9_16 | ~spl9_30),
% 2.25/0.70    inference(avatar_split_clause,[],[f518,f473,f298,f524,f520])).
% 2.25/0.70  fof(f298,plain,(
% 2.25/0.70    spl9_16 <=> ! [X1] : k1_setfam_1(k2_tarski(X1,k2_struct_0(sK3))) = k9_subset_1(u1_struct_0(sK3),X1,k2_struct_0(sK3))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.25/0.70  fof(f473,plain,(
% 2.25/0.70    spl9_30 <=> ! [X0] : (v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 2.25/0.70  fof(f518,plain,(
% 2.25/0.70    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3) | (~spl9_16 | ~spl9_30)),
% 2.25/0.70    inference(forward_demodulation,[],[f517,f299])).
% 2.25/0.70  fof(f299,plain,(
% 2.25/0.70    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,k2_struct_0(sK3))) = k9_subset_1(u1_struct_0(sK3),X1,k2_struct_0(sK3))) ) | ~spl9_16),
% 2.25/0.70    inference(avatar_component_clause,[],[f298])).
% 2.25/0.70  fof(f517,plain,(
% 2.25/0.70    v3_pre_topc(k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))),sK3) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl9_16 | ~spl9_30)),
% 2.25/0.70    inference(forward_demodulation,[],[f515,f299])).
% 2.25/0.70  fof(f515,plain,(
% 2.25/0.70    v3_pre_topc(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),sK3) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl9_30),
% 2.25/0.70    inference(resolution,[],[f474,f54])).
% 2.25/0.70  fof(f54,plain,(
% 2.25/0.70    m1_pre_topc(sK3,sK1)),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f474,plain,(
% 2.25/0.70    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl9_30),
% 2.25/0.70    inference(avatar_component_clause,[],[f473])).
% 2.25/0.70  fof(f475,plain,(
% 2.25/0.70    ~spl9_1 | ~spl9_18 | spl9_30),
% 2.25/0.70    inference(avatar_split_clause,[],[f469,f473,f351,f111])).
% 2.25/0.70  fof(f111,plain,(
% 2.25/0.70    spl9_1 <=> l1_pre_topc(sK1)),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.25/0.70  fof(f351,plain,(
% 2.25/0.70    spl9_18 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 2.25/0.70  fof(f469,plain,(
% 2.25/0.70    ( ! [X0] : (v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK4,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 2.25/0.70    inference(resolution,[],[f94,f88])).
% 2.25/0.70  fof(f88,plain,(
% 2.25/0.70    v3_pre_topc(sK4,sK1)),
% 2.25/0.70    inference(definition_unfolding,[],[f55,f57])).
% 2.25/0.70  fof(f57,plain,(
% 2.25/0.70    sK2 = sK4),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f55,plain,(
% 2.25/0.70    v3_pre_topc(sK2,sK1)),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f94,plain,(
% 2.25/0.70    ( ! [X0,X3,X1] : (~v3_pre_topc(X3,X0) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(equality_resolution,[],[f80])).
% 2.25/0.70  fof(f80,plain,(
% 2.25/0.70    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f50])).
% 2.25/0.70  fof(f50,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK8(X0,X1,X2),X0) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).
% 2.25/0.70  fof(f49,plain,(
% 2.25/0.70    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK8(X0,X1,X2),X0) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f48,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(rectify,[],[f47])).
% 2.25/0.70  fof(f47,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(nnf_transformation,[],[f23])).
% 2.25/0.70  fof(f23,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f13])).
% 2.25/0.70  fof(f13,axiom,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).
% 2.25/0.70  fof(f360,plain,(
% 2.25/0.70    spl9_18),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f358])).
% 2.25/0.70  fof(f358,plain,(
% 2.25/0.70    $false | spl9_18),
% 2.25/0.70    inference(resolution,[],[f353,f89])).
% 2.25/0.70  fof(f89,plain,(
% 2.25/0.70    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.25/0.70    inference(definition_unfolding,[],[f53,f57])).
% 2.25/0.70  fof(f53,plain,(
% 2.25/0.70    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f353,plain,(
% 2.25/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | spl9_18),
% 2.25/0.70    inference(avatar_component_clause,[],[f351])).
% 2.25/0.70  fof(f308,plain,(
% 2.25/0.70    spl9_15),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f307])).
% 2.25/0.70  fof(f307,plain,(
% 2.25/0.70    $false | spl9_15),
% 2.25/0.70    inference(resolution,[],[f296,f97])).
% 2.25/0.70  fof(f97,plain,(
% 2.25/0.70    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.25/0.70    inference(forward_demodulation,[],[f60,f59])).
% 2.25/0.70  fof(f59,plain,(
% 2.25/0.70    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.25/0.70    inference(cnf_transformation,[],[f2])).
% 2.25/0.70  fof(f2,axiom,(
% 2.25/0.70    ! [X0] : k2_subset_1(X0) = X0),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.25/0.70  fof(f60,plain,(
% 2.25/0.70    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.25/0.70    inference(cnf_transformation,[],[f3])).
% 2.25/0.70  fof(f3,axiom,(
% 2.25/0.70    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.25/0.70  fof(f296,plain,(
% 2.25/0.70    ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) | spl9_15),
% 2.25/0.70    inference(avatar_component_clause,[],[f294])).
% 2.25/0.70  fof(f294,plain,(
% 2.25/0.70    spl9_15 <=> m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))),
% 2.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.25/0.70  fof(f305,plain,(
% 2.25/0.70    ~spl9_15 | spl9_16 | ~spl9_7),
% 2.25/0.70    inference(avatar_split_clause,[],[f291,f188,f298,f294])).
% 2.25/0.70  fof(f291,plain,(
% 2.25/0.70    ( ! [X0] : (k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))) ) | ~spl9_7),
% 2.25/0.70    inference(superposition,[],[f91,f244])).
% 2.25/0.70  fof(f244,plain,(
% 2.25/0.70    ( ! [X4] : (k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = k9_subset_1(k2_struct_0(sK3),X4,k2_struct_0(sK3))) ) | ~spl9_7),
% 2.25/0.70    inference(resolution,[],[f241,f189])).
% 2.25/0.70  fof(f241,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X0))) )),
% 2.25/0.70    inference(resolution,[],[f230,f62])).
% 2.25/0.70  fof(f62,plain,(
% 2.25/0.70    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f19])).
% 2.25/0.70  fof(f19,plain,(
% 2.25/0.70    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f10])).
% 2.25/0.70  fof(f10,axiom,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.25/0.70  fof(f230,plain,(
% 2.25/0.70    ( ! [X4,X5] : (~l1_struct_0(X4) | k9_subset_1(u1_struct_0(X4),X5,k2_struct_0(X4)) = k9_subset_1(k2_struct_0(X4),X5,k2_struct_0(X4))) )),
% 2.25/0.70    inference(resolution,[],[f139,f61])).
% 2.25/0.70  fof(f61,plain,(
% 2.25/0.70    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f18])).
% 2.25/0.70  fof(f18,plain,(
% 2.25/0.70    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f9])).
% 2.25/0.70  fof(f9,axiom,(
% 2.25/0.70    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 2.25/0.70  fof(f139,plain,(
% 2.25/0.70    ( ! [X24,X23,X22] : (~m1_subset_1(X24,k1_zfmisc_1(X22)) | k9_subset_1(X22,X23,X24) = k9_subset_1(X24,X23,X24)) )),
% 2.25/0.70    inference(resolution,[],[f99,f97])).
% 2.25/0.70  fof(f99,plain,(
% 2.25/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X3)) | k9_subset_1(X2,X0,X1) = k9_subset_1(X3,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 2.25/0.70    inference(superposition,[],[f91,f91])).
% 2.25/0.70  fof(f91,plain,(
% 2.25/0.70    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.25/0.70    inference(definition_unfolding,[],[f87,f83])).
% 2.25/0.70  fof(f83,plain,(
% 2.25/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.25/0.70    inference(cnf_transformation,[],[f5])).
% 2.25/0.70  fof(f5,axiom,(
% 2.25/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.25/0.70  fof(f87,plain,(
% 2.25/0.70    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.25/0.70    inference(cnf_transformation,[],[f29])).
% 2.25/0.70  fof(f29,plain,(
% 2.25/0.70    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.25/0.70    inference(ennf_transformation,[],[f4])).
% 2.25/0.70  fof(f4,axiom,(
% 2.25/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.25/0.70  fof(f210,plain,(
% 2.25/0.70    ~spl9_7 | spl9_9 | ~spl9_7),
% 2.25/0.70    inference(avatar_split_clause,[],[f206,f188,f208,f188])).
% 2.25/0.70  fof(f206,plain,(
% 2.25/0.70    ( ! [X0] : (k2_struct_0(k1_pre_topc(sK3,X0)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK3,X0)),k2_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)) ) | ~spl9_7),
% 2.25/0.70    inference(resolution,[],[f204,f86])).
% 2.25/0.70  fof(f204,plain,(
% 2.25/0.70    ( ! [X9] : (~m1_pre_topc(X9,sK3) | k2_struct_0(X9) = k1_setfam_1(k2_tarski(k2_struct_0(X9),k2_struct_0(sK3)))) ) | ~spl9_7),
% 2.25/0.70    inference(resolution,[],[f189,f103])).
% 2.25/0.70  fof(f103,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1)))) )),
% 2.25/0.70    inference(duplicate_literal_removal,[],[f102])).
% 2.25/0.70  fof(f102,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 2.25/0.70    inference(condensation,[],[f101])).
% 2.25/0.70  fof(f101,plain,(
% 2.25/0.70    ( ! [X2,X3,X1] : (~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2) | k2_struct_0(X1) = k1_setfam_1(k2_tarski(k2_struct_0(X1),k2_struct_0(X2))) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X3)) )),
% 2.25/0.70    inference(resolution,[],[f98,f75])).
% 2.25/0.70  fof(f75,plain,(
% 2.25/0.70    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f21])).
% 2.25/0.70  fof(f21,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f11])).
% 2.25/0.70  fof(f11,axiom,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.25/0.70  fof(f98,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | k2_struct_0(X0) = k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1)))) )),
% 2.25/0.70    inference(resolution,[],[f71,f90])).
% 2.25/0.70  fof(f90,plain,(
% 2.25/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.25/0.70    inference(definition_unfolding,[],[f84,f83])).
% 2.25/0.70  fof(f84,plain,(
% 2.25/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f26])).
% 2.25/0.70  fof(f26,plain,(
% 2.25/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.25/0.70    inference(ennf_transformation,[],[f1])).
% 2.25/0.70  fof(f1,axiom,(
% 2.25/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.25/0.70  fof(f71,plain,(
% 2.25/0.70    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.70    inference(cnf_transformation,[],[f46])).
% 2.25/0.70  fof(f46,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (~sP0(sK7(X0,X1),X1,X0) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X3] : (sP0(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 2.25/0.70  fof(f45,plain,(
% 2.25/0.70    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~sP0(sK7(X0,X1),X1,X0) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.25/0.70    introduced(choice_axiom,[])).
% 2.25/0.70  fof(f44,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X3] : (sP0(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(rectify,[],[f43])).
% 2.25/0.70  fof(f43,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(flattening,[],[f42])).
% 2.25/0.70  fof(f42,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(nnf_transformation,[],[f31])).
% 2.25/0.70  fof(f31,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(definition_folding,[],[f20,f30])).
% 2.25/0.70  fof(f30,plain,(
% 2.25/0.70    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.25/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.25/0.70  fof(f20,plain,(
% 2.25/0.70    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.70    inference(ennf_transformation,[],[f7])).
% 2.25/0.70  fof(f7,axiom,(
% 2.25/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.25/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 2.25/0.70  fof(f199,plain,(
% 2.25/0.70    spl9_7),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f197])).
% 2.25/0.70  fof(f197,plain,(
% 2.25/0.70    $false | spl9_7),
% 2.25/0.70    inference(resolution,[],[f196,f52])).
% 2.25/0.70  fof(f52,plain,(
% 2.25/0.70    l1_pre_topc(sK1)),
% 2.25/0.70    inference(cnf_transformation,[],[f36])).
% 2.25/0.70  fof(f196,plain,(
% 2.25/0.70    ~l1_pre_topc(sK1) | spl9_7),
% 2.25/0.70    inference(resolution,[],[f195,f54])).
% 2.25/0.70  fof(f195,plain,(
% 2.25/0.70    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl9_7),
% 2.25/0.70    inference(resolution,[],[f190,f75])).
% 2.25/0.70  fof(f190,plain,(
% 2.25/0.70    ~l1_pre_topc(sK3) | spl9_7),
% 2.25/0.70    inference(avatar_component_clause,[],[f188])).
% 2.25/0.70  fof(f163,plain,(
% 2.25/0.70    spl9_3),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f161])).
% 2.25/0.70  fof(f161,plain,(
% 2.25/0.70    $false | spl9_3),
% 2.25/0.70    inference(resolution,[],[f155,f56])).
% 2.25/0.70  fof(f155,plain,(
% 2.25/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | spl9_3),
% 2.25/0.70    inference(avatar_component_clause,[],[f153])).
% 2.25/0.70  fof(f120,plain,(
% 2.25/0.70    spl9_1),
% 2.25/0.70    inference(avatar_contradiction_clause,[],[f118])).
% 2.25/0.70  fof(f118,plain,(
% 2.25/0.70    $false | spl9_1),
% 2.25/0.70    inference(resolution,[],[f113,f52])).
% 2.25/0.70  fof(f113,plain,(
% 2.25/0.70    ~l1_pre_topc(sK1) | spl9_1),
% 2.25/0.70    inference(avatar_component_clause,[],[f111])).
% 2.25/0.70  % SZS output end Proof for theBenchmark
% 2.25/0.70  % (4518)------------------------------
% 2.25/0.70  % (4518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.70  % (4518)Termination reason: Refutation
% 2.25/0.70  
% 2.25/0.70  % (4518)Memory used [KB]: 6652
% 2.25/0.70  % (4518)Time elapsed: 0.274 s
% 2.25/0.70  % (4518)------------------------------
% 2.25/0.70  % (4518)------------------------------
% 2.56/0.73  % (4505)Success in time 0.357 s
%------------------------------------------------------------------------------
