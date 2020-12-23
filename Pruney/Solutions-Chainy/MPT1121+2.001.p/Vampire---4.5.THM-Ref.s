%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:17 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 486 expanded)
%              Number of leaves         :   18 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          :  525 (3241 expanded)
%              Number of equality atoms :   42 ( 683 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f89,f90,f111,f172])).

fof(f172,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f167,f158])).

fof(f158,plain,
    ( r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f157,plain,
    ( r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f156,f43])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( ~ v4_pre_topc(sK1,sK0)
        & sK1 = k2_pre_topc(sK0,sK1)
        & v2_pre_topc(sK0) )
      | ( sK1 != k2_pre_topc(sK0,sK1)
        & v4_pre_topc(sK1,sK0) ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v4_pre_topc(X1,X0)
                & k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
              | ( k2_pre_topc(X0,X1) != X1
                & v4_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,sK0)
              & k2_pre_topc(sK0,X1) = X1
              & v2_pre_topc(sK0) )
            | ( k2_pre_topc(sK0,X1) != X1
              & v4_pre_topc(X1,sK0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ( ( ~ v4_pre_topc(X1,sK0)
            & k2_pre_topc(sK0,X1) = X1
            & v2_pre_topc(sK0) )
          | ( k2_pre_topc(sK0,X1) != X1
            & v4_pre_topc(X1,sK0) ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( ~ v4_pre_topc(sK1,sK0)
          & sK1 = k2_pre_topc(sK0,sK1)
          & v2_pre_topc(sK0) )
        | ( sK1 != k2_pre_topc(sK0,sK1)
          & v4_pre_topc(sK1,sK0) ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k2_pre_topc(X0,X1) = X1
                  & v2_pre_topc(X0) )
               => v4_pre_topc(X1,X0) )
              & ( v4_pre_topc(X1,X0)
               => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f156,plain,
    ( r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f155,f124])).

fof(f124,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f43,f44,f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
            & ! [X3] :
                ( ( ( r2_hidden(X3,sK3(X0,X1))
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,sK3(X0,X1)) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r1_tarski(X1,X3)
                  | ~ v4_pre_topc(X3,X0) )
                & ( ( r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3(X0,X1))
                | ~ r1_tarski(X1,X3)
                | ~ v4_pre_topc(X3,X0) )
              & ( ( r1_tarski(X1,X3)
                  & v4_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3(X0,X1)) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_pre_topc)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f155,plain,
    ( r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f149,f82])).

fof(f82,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f149,plain,
    ( v4_pre_topc(sK1,sK0)
    | r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f63,f126])).

fof(f126,plain,
    ( sK1 = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f125,f77])).

fof(f77,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_1
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f125,plain,
    ( k2_pre_topc(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f43,f44,f88,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK4(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

fof(f167,plain,
    ( ~ r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f88,f43,f44,f162,f154,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f154,plain,
    ( m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f153,f88])).

fof(f153,plain,
    ( m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f152,plain,
    ( m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f151,f124])).

fof(f151,plain,
    ( m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f148,f82])).

fof(f148,plain,
    ( v4_pre_topc(sK1,sK0)
    | m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f62,f126])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f161,f88])).

fof(f161,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f160,f43])).

fof(f160,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f159,f124])).

fof(f159,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f150,f82])).

fof(f150,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f64,f126])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f103,f108])).

fof(f108,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f92,f97,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f97,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f94,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f94,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f78,f91,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f43,f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f78,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f92,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f103,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f43,f81,f74,f44,f44,f98,f97,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK2(X0,X1,X2))
                    & r1_tarski(X1,sK2(X0,X1,X2))
                    & v4_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK2(X0,X1,X2))
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v4_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

fof(f98,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f90,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f45,f86,f80])).

fof(f45,plain,
    ( v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f46,f86,f76])).

fof(f46,plain,
    ( v2_pre_topc(sK0)
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,
    ( spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f47,f76,f80])).

fof(f47,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f50,f80,f76])).

fof(f50,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:37:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (20086)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20090)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (20088)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (20095)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20087)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20109)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (20084)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20085)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20105)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (20108)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (20097)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.55  % (20100)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.55  % (20101)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.55  % (20106)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.55  % (20098)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.55  % (20102)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.55  % (20104)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.55  % (20099)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.55  % (20089)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.55  % (20092)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.55  % (20111)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.55  % (20091)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.56  % (20096)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.56  % (20093)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.56  % (20094)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.56  % (20083)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.56  % (20112)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.56  % (20110)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.56  % (20107)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.56  % (20109)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f173,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(avatar_sat_refutation,[],[f83,f84,f89,f90,f111,f172])).
% 1.53/0.56  fof(f172,plain,(
% 1.53/0.56    ~spl6_1 | spl6_2 | ~spl6_3),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f171])).
% 1.53/0.56  fof(f171,plain,(
% 1.53/0.56    $false | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f167,f158])).
% 1.53/0.56  fof(f158,plain,(
% 1.53/0.56    r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f157,f88])).
% 1.53/0.56  fof(f88,plain,(
% 1.53/0.56    v2_pre_topc(sK0) | ~spl6_3),
% 1.53/0.56    inference(avatar_component_clause,[],[f86])).
% 1.53/0.56  fof(f86,plain,(
% 1.53/0.56    spl6_3 <=> v2_pre_topc(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.53/0.56  fof(f157,plain,(
% 1.53/0.56    r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f156,f43])).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    l1_pre_topc(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    (((~v4_pre_topc(sK1,sK0) & sK1 = k2_pre_topc(sK0,sK1) & v2_pre_topc(sK0)) | (sK1 != k2_pre_topc(sK0,sK1) & v4_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v4_pre_topc(X1,sK0) & k2_pre_topc(sK0,X1) = X1 & v2_pre_topc(sK0)) | (k2_pre_topc(sK0,X1) != X1 & v4_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ? [X1] : (((~v4_pre_topc(X1,sK0) & k2_pre_topc(sK0,X1) = X1 & v2_pre_topc(sK0)) | (k2_pre_topc(sK0,X1) != X1 & v4_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (((~v4_pre_topc(sK1,sK0) & sK1 = k2_pre_topc(sK0,sK1) & v2_pre_topc(sK0)) | (sK1 != k2_pre_topc(sK0,sK1) & v4_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f12,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f11])).
% 1.53/0.56  fof(f11,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & (k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0))) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f10])).
% 1.53/0.56  fof(f10,negated_conjecture,(
% 1.53/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.53/0.56    inference(negated_conjecture,[],[f9])).
% 1.53/0.56  fof(f9,conjecture,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.53/0.56  fof(f156,plain,(
% 1.53/0.56    r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f155,f124])).
% 1.53/0.56  fof(f124,plain,(
% 1.53/0.56    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_3),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f43,f44,f88,f57])).
% 1.53/0.56  fof(f57,plain,(
% 1.53/0.56    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f34,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.53/0.56  fof(f33,plain,(
% 1.53/0.56    ! [X1,X0] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f32,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f16])).
% 1.53/0.56  fof(f16,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_pre_topc)).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f155,plain,(
% 1.53/0.56    r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f149,f82])).
% 1.53/0.56  fof(f82,plain,(
% 1.53/0.56    ~v4_pre_topc(sK1,sK0) | spl6_2),
% 1.53/0.56    inference(avatar_component_clause,[],[f80])).
% 1.53/0.56  fof(f80,plain,(
% 1.53/0.56    spl6_2 <=> v4_pre_topc(sK1,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.53/0.56  fof(f149,plain,(
% 1.53/0.56    v4_pre_topc(sK1,sK0) | r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_3)),
% 1.53/0.56    inference(superposition,[],[f63,f126])).
% 1.53/0.56  fof(f126,plain,(
% 1.53/0.56    sK1 = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1)) | (~spl6_1 | ~spl6_3)),
% 1.53/0.56    inference(forward_demodulation,[],[f125,f77])).
% 1.53/0.56  fof(f77,plain,(
% 1.53/0.56    sK1 = k2_pre_topc(sK0,sK1) | ~spl6_1),
% 1.53/0.56    inference(avatar_component_clause,[],[f76])).
% 1.53/0.56  fof(f76,plain,(
% 1.53/0.56    spl6_1 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.53/0.56  fof(f125,plain,(
% 1.53/0.56    k2_pre_topc(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1)) | ~spl6_3),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f43,f44,f88,f61])).
% 1.53/0.56  fof(f61,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f63,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f35])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f19,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : ((~v4_pre_topc(X2,X0) & r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).
% 1.53/0.56  fof(f167,plain,(
% 1.53/0.56    ~r2_hidden(sK4(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f88,f43,f44,f162,f154,f58])).
% 1.53/0.56  fof(f58,plain,(
% 1.53/0.56    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f154,plain,(
% 1.53/0.56    m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f153,f88])).
% 1.53/0.56  fof(f153,plain,(
% 1.53/0.56    m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f152,f43])).
% 1.53/0.56  fof(f152,plain,(
% 1.53/0.56    m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f151,f124])).
% 1.53/0.56  fof(f151,plain,(
% 1.53/0.56    m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f148,f82])).
% 1.53/0.56  fof(f148,plain,(
% 1.53/0.56    v4_pre_topc(sK1,sK0) | m1_subset_1(sK4(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_3)),
% 1.53/0.56    inference(superposition,[],[f62,f126])).
% 1.53/0.56  fof(f62,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f162,plain,(
% 1.53/0.56    ~v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f161,f88])).
% 1.53/0.56  fof(f161,plain,(
% 1.53/0.56    ~v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f160,f43])).
% 1.53/0.56  fof(f160,plain,(
% 1.53/0.56    ~v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f159,f124])).
% 1.53/0.56  fof(f159,plain,(
% 1.53/0.56    ~v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f150,f82])).
% 1.53/0.56  fof(f150,plain,(
% 1.53/0.56    v4_pre_topc(sK1,sK0) | ~v4_pre_topc(sK4(sK0,sK3(sK0,sK1)),sK0) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_3)),
% 1.53/0.56    inference(superposition,[],[f64,f126])).
% 1.53/0.56  fof(f64,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(sK4(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f111,plain,(
% 1.53/0.56    spl6_1 | ~spl6_2),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f110])).
% 1.53/0.56  fof(f110,plain,(
% 1.53/0.56    $false | (spl6_1 | ~spl6_2)),
% 1.53/0.56    inference(subsumption_resolution,[],[f103,f108])).
% 1.53/0.56  fof(f108,plain,(
% 1.53/0.56    r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0)) | spl6_1),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f92,f97,f65])).
% 1.53/0.56  fof(f65,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.53/0.56  fof(f97,plain,(
% 1.53/0.56    r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) | spl6_1),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f94,f71])).
% 1.53/0.56  fof(f71,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f42])).
% 1.53/0.56  fof(f42,plain,(
% 1.53/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f40,plain,(
% 1.53/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.56    inference(rectify,[],[f39])).
% 1.53/0.56  fof(f39,plain,(
% 1.53/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.56    inference(nnf_transformation,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f1])).
% 1.53/0.56  fof(f1,axiom,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.56  fof(f94,plain,(
% 1.53/0.56    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | spl6_1),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f78,f91,f69])).
% 1.53/0.56  fof(f69,plain,(
% 1.53/0.56    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f38])).
% 1.53/0.56  fof(f38,plain,(
% 1.53/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.56    inference(flattening,[],[f37])).
% 1.53/0.56  fof(f37,plain,(
% 1.53/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.56    inference(nnf_transformation,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.56  fof(f91,plain,(
% 1.53/0.56    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f43,f44,f51])).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f13])).
% 1.53/0.56  fof(f13,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.53/0.56  fof(f78,plain,(
% 1.53/0.56    sK1 != k2_pre_topc(sK0,sK1) | spl6_1),
% 1.53/0.56    inference(avatar_component_clause,[],[f76])).
% 1.53/0.56  fof(f92,plain,(
% 1.53/0.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f43,f44,f66])).
% 1.53/0.56  fof(f66,plain,(
% 1.53/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f22])).
% 1.53/0.56  fof(f22,plain,(
% 1.53/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f21])).
% 1.53/0.56  fof(f21,plain,(
% 1.53/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.53/0.56  fof(f103,plain,(
% 1.53/0.56    ~r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f43,f81,f74,f44,f44,f98,f97,f52])).
% 1.53/0.56  fof(f52,plain,(
% 1.53/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f28,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(rectify,[],[f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f15])).
% 1.53/0.56  fof(f15,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f14])).
% 1.53/0.56  fof(f14,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).
% 1.53/0.56  fof(f98,plain,(
% 1.53/0.56    ~r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1) | spl6_1),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f94,f72])).
% 1.53/0.56  fof(f72,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f42])).
% 1.53/0.56  fof(f74,plain,(
% 1.53/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.56    inference(equality_resolution,[],[f67])).
% 1.53/0.56  fof(f67,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f38])).
% 1.53/0.56  fof(f81,plain,(
% 1.53/0.56    v4_pre_topc(sK1,sK0) | ~spl6_2),
% 1.53/0.56    inference(avatar_component_clause,[],[f80])).
% 1.53/0.56  fof(f90,plain,(
% 1.53/0.56    spl6_2 | spl6_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f45,f86,f80])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f89,plain,(
% 1.53/0.56    ~spl6_1 | spl6_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f46,f86,f76])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    v2_pre_topc(sK0) | sK1 != k2_pre_topc(sK0,sK1)),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f84,plain,(
% 1.53/0.56    spl6_2 | spl6_1),
% 1.53/0.56    inference(avatar_split_clause,[],[f47,f76,f80])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f83,plain,(
% 1.53/0.56    ~spl6_1 | ~spl6_2),
% 1.53/0.56    inference(avatar_split_clause,[],[f50,f80,f76])).
% 1.53/0.56  fof(f50,plain,(
% 1.53/0.56    ~v4_pre_topc(sK1,sK0) | sK1 != k2_pre_topc(sK0,sK1)),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (20109)------------------------------
% 1.53/0.56  % (20109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (20109)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (20109)Memory used [KB]: 10874
% 1.53/0.56  % (20109)Time elapsed: 0.150 s
% 1.53/0.56  % (20109)------------------------------
% 1.53/0.56  % (20109)------------------------------
% 1.53/0.57  % (20082)Success in time 0.201 s
%------------------------------------------------------------------------------
