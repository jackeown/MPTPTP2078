%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t3_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  68 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 351 expanded)
%              Number of equality atoms :   26 ( 107 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f86,f93,f100,f103])).

fof(f103,plain,
    ( ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f101,f92])).

fof(f92,plain,
    ( m1_setfam_1(sK2,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_6
  <=> m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f101,plain,
    ( ~ m1_setfam_1(sK2,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f99,f46])).

fof(f46,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
    & m1_setfam_1(sK2,u1_struct_0(sK0))
    & sK2 = sK3
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ m1_setfam_1(X3,u1_struct_0(X1))
            & m1_setfam_1(X2,u1_struct_0(X0))
            & X2 = X3
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
   => ( ? [X3] :
          ( ~ m1_setfam_1(X3,u1_struct_0(sK1))
          & m1_setfam_1(sK2,u1_struct_0(sK0))
          & sK2 = X3
          & u1_struct_0(sK0) = u1_struct_0(sK1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_setfam_1(X3,u1_struct_0(X1))
          & m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ m1_setfam_1(sK3,u1_struct_0(X1))
        & m1_setfam_1(X2,u1_struct_0(X0))
        & sK3 = X2
        & u1_struct_0(X0) = u1_struct_0(X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ m1_setfam_1(X3,u1_struct_0(X1))
          & m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ m1_setfam_1(X3,u1_struct_0(X1))
          & m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                & X2 = X3
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                        & X2 = X3
                        & u1_struct_0(X0) = u1_struct_0(X1) )
                     => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                      & X2 = X3
                      & u1_struct_0(X0) = u1_struct_0(X1) )
                   => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t3_waybel_9.p',t3_waybel_9)).

fof(f99,plain,
    ( ~ m1_setfam_1(sK2,u1_struct_0(sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_9
  <=> ~ m1_setfam_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f100,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f62,f98])).

fof(f62,plain,(
    ~ m1_setfam_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f47,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    ~ m1_setfam_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f84])).

fof(f84,plain,
    ( spl6_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f51,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t3_waybel_9.p',d2_xboole_0)).

fof(f79,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f47,f77])).

fof(f77,plain,
    ( spl6_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f50,f70])).

fof(f70,plain,
    ( spl6_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t3_waybel_9.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
