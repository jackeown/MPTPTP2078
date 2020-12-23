%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 712 expanded)
%              Number of leaves         :   15 ( 173 expanded)
%              Depth                    :   37
%              Number of atoms          :  827 (6045 expanded)
%              Number of equality atoms :   84 ( 968 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f979,plain,(
    $false ),
    inference(subsumption_resolution,[],[f978,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_tsep_1(sK2,sK1) )
    & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
      | ( m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1) ) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1)
            | ~ m1_pre_topc(X1,sK1)
            | ~ v1_tsep_1(X1,sK1) )
          & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1)
            | ( m1_pre_topc(X1,sK1)
              & v1_tsep_1(X1,sK1) ) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1)
          | ~ m1_pre_topc(X1,sK1)
          | ~ v1_tsep_1(X1,sK1) )
        & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1)
          | ( m1_pre_topc(X1,sK1)
            & v1_tsep_1(X1,sK1) ) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | ~ v1_tsep_1(sK2,sK1) )
      & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
        | ( m1_pre_topc(sK2,sK1)
          & v1_tsep_1(sK2,sK1) ) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f978,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f973,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f973,plain,(
    ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f972,f55])).

fof(f972,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f971,f54])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f971,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f963,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f963,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f959,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
            & r1_tarski(sK5(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f959,plain,(
    ! [X5] :
      ( ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f958,f686])).

fof(f686,plain,(
    ~ v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f685,f55])).

fof(f685,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f684,f57])).

fof(f57,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f684,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f683])).

fof(f683,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f665,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f89,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK6(X0,X1),X0)
                & u1_struct_0(X1) = sK6(X0,X1)
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK6(X0,X1),X0)
        & u1_struct_0(X1) = sK6(X0,X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

% (5976)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f665,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f664,f57])).

fof(f664,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f663,f55])).

fof(f663,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1) ),
    inference(resolution,[],[f661,f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( r2_hidden(u1_struct_0(X2),u1_pre_topc(X3))
      | ~ v3_pre_topc(u1_struct_0(X2),X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ v3_pre_topc(u1_struct_0(X2),X3)
      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f80,f75])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f661,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f660,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f660,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f654,f57])).

fof(f654,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) ),
    inference(equality_resolution,[],[f381])).

fof(f381,plain,(
    ! [X0] :
      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0)
      | ~ v1_tsep_1(sK2,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f380,f53])).

fof(f380,plain,(
    ! [X0] :
      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0)
      | ~ v1_tsep_1(sK2,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f379,f54])).

fof(f379,plain,(
    ! [X0] :
      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0)
      | ~ v1_tsep_1(sK2,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f378,f55])).

fof(f378,plain,(
    ! [X0] :
      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0)
      | ~ v1_tsep_1(sK2,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f328,f57])).

fof(f328,plain,(
    ! [X0] :
      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_tsep_1(sK2,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1)) ) ),
    inference(superposition,[],[f60,f246])).

fof(f246,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f161,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f192,f75])).

fof(f192,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f82,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f75])).

fof(f90,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f160,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f143,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f62,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f60,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f958,plain,(
    ! [X5] :
      ( ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f957,f55])).

fof(f957,plain,(
    ! [X5] :
      ( ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(sK1)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f955,f57])).

fof(f955,plain,(
    ! [X5] :
      ( ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ l1_pre_topc(sK1)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(resolution,[],[f928,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f136,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK6(X0,X1)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X1,X0),u1_pre_topc(X1))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | v1_tsep_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f135,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK6(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(sK6(X1,X0),u1_pre_topc(X1))
      | v3_pre_topc(sK6(X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(sK6(X1,X0),u1_pre_topc(X1))
      | v3_pre_topc(sK6(X1,X0),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f928,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f927,f686])).

fof(f927,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f926,f56])).

fof(f926,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f925,f57])).

fof(f925,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f924,f53])).

fof(f924,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f923,f54])).

fof(f923,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f906,f55])).

fof(f906,plain,(
    ! [X5] :
      ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(trivial_inequality_removal,[],[f886])).

fof(f886,plain,(
    ! [X5] :
      ( u1_pre_topc(sK1) != u1_pre_topc(sK1)
      | r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X5)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(superposition,[],[f198,f480])).

fof(f480,plain,(
    ! [X10] :
      ( u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2))
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f479,f53])).

% (5979)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f479,plain,(
    ! [X10] :
      ( u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2))
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f478,f54])).

fof(f478,plain,(
    ! [X10] :
      ( u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2))
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f434,f55])).

fof(f434,plain,(
    ! [X10] :
      ( u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2))
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | v1_tsep_1(sK2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f396])).

fof(f396,plain,(
    ! [X10] :
      ( u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2))
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X10,sK1)
      | v2_struct_0(X10)
      | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1))
      | v1_tsep_1(sK2,sK1) ) ),
    inference(superposition,[],[f193,f377])).

fof(f377,plain,(
    ! [X1] :
      ( k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1))
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f376,f53])).

fof(f376,plain,(
    ! [X1] :
      ( k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1))
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f375,f54])).

fof(f375,plain,(
    ! [X1] :
      ( k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1))
      | v1_tsep_1(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f325,f55])).

fof(f325,plain,(
    ! [X1] :
      ( k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1))
      | v1_tsep_1(sK2,sK1) ) ),
    inference(superposition,[],[f246,f58])).

fof(f58,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f198,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1))
      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f197,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1))
      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1))
      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f83,f92])).

fof(f83,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:41:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (5977)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (5964)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (5969)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (5973)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (5959)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (5972)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (5961)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (5960)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (5965)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (5960)Refutation not found, incomplete strategy% (5960)------------------------------
% 0.20/0.49  % (5960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5960)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5960)Memory used [KB]: 10618
% 0.20/0.49  % (5960)Time elapsed: 0.082 s
% 0.20/0.49  % (5960)------------------------------
% 0.20/0.49  % (5960)------------------------------
% 0.20/0.49  % (5972)Refutation not found, incomplete strategy% (5972)------------------------------
% 0.20/0.49  % (5972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5972)Memory used [KB]: 1791
% 0.20/0.49  % (5972)Time elapsed: 0.087 s
% 0.20/0.49  % (5972)------------------------------
% 0.20/0.49  % (5972)------------------------------
% 0.20/0.49  % (5963)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (5974)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (5977)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f979,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f978,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ? [X1] : ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.20/0.49  fof(f978,plain,(
% 0.20/0.49    ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f973,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.49  fof(f973,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f972,f55])).
% 0.20/0.49  fof(f972,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f971,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    v2_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f971,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f963,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f963,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f959,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f19,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.49    inference(rectify,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.49  fof(f959,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f958,f686])).
% 0.20/0.49  fof(f686,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f685,f55])).
% 0.20/0.49  fof(f685,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f684,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f684,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f683])).
% 0.20/0.49  fof(f683,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f665,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f89,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK6(X0,X1),X0) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK6(X0,X1),X0) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f47])).
% 0.20/0.49  % (5976)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.20/0.49  fof(f665,plain,(
% 0.20/0.49    ~v3_pre_topc(u1_struct_0(sK2),sK1) | ~v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f664,f57])).
% 0.20/0.49  fof(f664,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK2),sK1) | ~m1_pre_topc(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f663,f55])).
% 0.20/0.49  fof(f663,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~v3_pre_topc(u1_struct_0(sK2),sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f661,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X2,X3] : (r2_hidden(u1_struct_0(X2),u1_pre_topc(X3)) | ~v3_pre_topc(u1_struct_0(X2),X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X2,X3)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~v3_pre_topc(u1_struct_0(X2),X3) | r2_hidden(u1_struct_0(X2),u1_pre_topc(X3)) | ~l1_pre_topc(X3) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 0.20/0.49    inference(resolution,[],[f80,f75])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.49  fof(f661,plain,(
% 0.20/0.49    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f660,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f660,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f654,f57])).
% 0.20/0.49  fof(f654,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1))),
% 0.20/0.49    inference(equality_resolution,[],[f381])).
% 0.20/0.49  fof(f381,plain,(
% 0.20/0.49    ( ! [X0] : (k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f380,f53])).
% 0.20/0.49  fof(f380,plain,(
% 0.20/0.49    ( ! [X0] : (k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f379,f54])).
% 0.20/0.49  fof(f379,plain,(
% 0.20/0.49    ( ! [X0] : (k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f378,f55])).
% 0.20/0.49  fof(f378,plain,(
% 0.20/0.49    ( ! [X0] : (k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f328,f57])).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    ( ! [X0] : (k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,X0) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK1))) )),
% 0.20/0.49    inference(superposition,[],[f60,f246])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f230])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(superposition,[],[f161,f193])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1)) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f192,f75])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1)) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(X0,X1)) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f82,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f75])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f160,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f143,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(k8_tmap_1(X0,X1))) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f62,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f958,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f957,f55])).
% 0.20/0.49  fof(f957,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~l1_pre_topc(sK1) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f955,f57])).
% 0.20/0.49  fof(f955,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f928,f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(superposition,[],[f136,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X1) = sK6(X0,X1) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK6(X1,X0),u1_pre_topc(X1)) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | v1_tsep_1(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f135,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_pre_topc(sK6(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r2_hidden(sK6(X1,X0),u1_pre_topc(X1)) | v3_pre_topc(sK6(X1,X0),X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r2_hidden(sK6(X1,X0),u1_pre_topc(X1)) | v3_pre_topc(sK6(X1,X0),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(resolution,[],[f77,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f51])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f928,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f927,f686])).
% 0.20/0.49  fof(f927,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f926,f56])).
% 0.20/0.49  fof(f926,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f925,f57])).
% 0.20/0.49  fof(f925,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f924,f53])).
% 0.20/0.49  fof(f924,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f923,f54])).
% 0.20/0.49  fof(f923,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f906,f55])).
% 0.20/0.49  fof(f906,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f886])).
% 0.20/0.49  fof(f886,plain,(
% 0.20/0.49    ( ! [X5] : (u1_pre_topc(sK1) != u1_pre_topc(sK1) | r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~r2_hidden(u1_struct_0(X5),u1_pre_topc(sK1)) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X5) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(superposition,[],[f198,f480])).
% 0.20/0.49  fof(f480,plain,(
% 0.20/0.49    ( ! [X10] : (u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2)) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f479,f53])).
% 0.20/0.49  % (5979)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  fof(f479,plain,(
% 0.20/0.49    ( ! [X10] : (u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2)) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f478,f54])).
% 0.20/0.49  fof(f478,plain,(
% 0.20/0.49    ( ! [X10] : (u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2)) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f434,f55])).
% 0.20/0.49  fof(f434,plain,(
% 0.20/0.49    ( ! [X10] : (u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2)) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f396])).
% 0.20/0.49  fof(f396,plain,(
% 0.20/0.49    ( ! [X10] : (u1_pre_topc(sK1) = u1_pre_topc(k8_tmap_1(sK1,sK2)) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | ~m1_pre_topc(X10,sK1) | v2_struct_0(X10) | ~r2_hidden(u1_struct_0(X10),u1_pre_topc(sK1)) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(superposition,[],[f193,f377])).
% 0.20/0.49  fof(f377,plain,(
% 0.20/0.49    ( ! [X1] : (k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1)) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f376,f53])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    ( ! [X1] : (k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1)) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f375,f54])).
% 0.20/0.49  fof(f375,plain,(
% 0.20/0.49    ( ! [X1] : (k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1)) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f325,f55])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    ( ! [X1] : (k8_tmap_1(sK1,X1) = k8_tmap_1(sK1,sK2) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(u1_struct_0(X1),u1_pre_topc(sK1)) | v1_tsep_1(sK2,sK1)) )),
% 0.20/0.49    inference(superposition,[],[f246,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1)) | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f75])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1)) | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) != u1_pre_topc(k8_tmap_1(X0,X1)) | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f83,f92])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5977)------------------------------
% 0.20/0.49  % (5977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5977)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5977)Memory used [KB]: 2302
% 0.20/0.49  % (5977)Time elapsed: 0.095 s
% 0.20/0.49  % (5977)------------------------------
% 0.20/0.49  % (5977)------------------------------
% 0.20/0.49  % (5966)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (5979)Refutation not found, incomplete strategy% (5979)------------------------------
% 0.20/0.50  % (5979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5958)Success in time 0.146 s
%------------------------------------------------------------------------------
