%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t79_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 (1768 expanded)
%              Number of leaves         :   15 ( 479 expanded)
%              Depth                    :   32
%              Number of atoms          :  464 (9115 expanded)
%              Number of equality atoms :   12 (  77 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4293,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4282,f3769])).

fof(f3769,plain,(
    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f3767,f77])).

fof(f77,plain,
    ( v2_tops_2(sK1,sK0)
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_tops_2(sK1,sK0) )
    & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ v2_tops_2(X1,X0) )
            & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ v2_tops_2(X1,sK0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | v2_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ v2_tops_2(sK1,X0) )
        & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
          | v2_tops_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',t79_tops_2)).

fof(f3767,plain,(
    ~ v2_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3766,f356])).

fof(f356,plain,
    ( r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',d3_tarski)).

fof(f78,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f3766,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    inference(subsumption_resolution,[],[f3752,f2706])).

fof(f2706,plain,(
    ! [X0] :
      ( ~ v2_tops_2(sK1,sK0)
      | ~ r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
      | ~ r1_tarski(X0,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f357,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f357,plain,
    ( ~ r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f78,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3752,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    inference(resolution,[],[f3741,f275])).

fof(f275,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f274,f135])).

fof(f135,plain,(
    ! [X9] :
      ( m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X9,sK1) ) ),
    inference(resolution,[],[f76,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',t4_subset)).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f274,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f273,f75])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f273,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f272,f76])).

fof(f272,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f77,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',d2_tops_2)).

fof(f3741,plain,
    ( ~ v4_pre_topc(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v2_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3679,f356])).

fof(f3679,plain,
    ( ~ r2_hidden(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v4_pre_topc(sK2(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f2918,f357])).

fof(f2918,plain,(
    ! [X25] :
      ( r2_hidden(X25,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ r2_hidden(X25,sK1)
      | ~ v4_pre_topc(X25,sK0) ) ),
    inference(subsumption_resolution,[],[f2917,f135])).

fof(f2917,plain,(
    ! [X25] :
      ( ~ v4_pre_topc(X25,sK0)
      | ~ r2_hidden(X25,sK1)
      | r2_hidden(X25,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2916,f109])).

fof(f109,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f75,f91])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',dt_u1_pre_topc)).

fof(f2916,plain,(
    ! [X25] :
      ( ~ v4_pre_topc(X25,sK0)
      | ~ r2_hidden(X25,sK1)
      | r2_hidden(X25,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f2913,f159])).

fof(f159,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f109,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',dt_k7_setfam_1)).

fof(f2913,plain,(
    ! [X25] :
      ( ~ v4_pre_topc(X25,sK0)
      | ~ r2_hidden(X25,sK1)
      | r2_hidden(X25,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f1161,f107])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',d8_setfam_1)).

fof(f1161,plain,(
    ! [X1] :
      ( r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
      | ~ v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f1160,f184])).

fof(f184,plain,(
    ! [X6] :
      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f135,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',dt_k3_subset_1)).

fof(f1160,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ v4_pre_topc(X1,sK0)
      | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1158,f75])).

fof(f1158,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ v4_pre_topc(X1,sK0)
      | r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f192,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',d5_pre_topc)).

fof(f192,plain,(
    ! [X2] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | ~ v4_pre_topc(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f181,f75])).

fof(f181,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X2),sK0)
      | ~ v4_pre_topc(X2,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f135,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t79_tops_2.p',t29_tops_1)).

fof(f4282,plain,(
    ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f4223,f3797])).

fof(f3797,plain,(
    ! [X5] :
      ( r2_hidden(sK4(sK0,sK1),X5)
      | ~ r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f3771,f81])).

fof(f3771,plain,(
    r2_hidden(sK4(sK0,sK1),sK1) ),
    inference(resolution,[],[f3767,f141])).

fof(f141,plain,
    ( v2_tops_2(sK1,sK0)
    | r2_hidden(sK4(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f121,f75])).

fof(f121,plain,
    ( v2_tops_2(sK1,sK0)
    | r2_hidden(sK4(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4223,plain,(
    ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f4222,f109])).

fof(f4222,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f4221,f159])).

fof(f4221,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f4212,f3768])).

fof(f3768,plain,(
    m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3767,f140])).

fof(f140,plain,
    ( v2_tops_2(sK1,sK0)
    | m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f120,f75])).

fof(f120,plain,
    ( v2_tops_2(sK1,sK0)
    | m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4212,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f3891,f108])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f3891,plain,(
    ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3887,f3824])).

fof(f3824,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3768,f102])).

fof(f3887,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),u1_pre_topc(sK0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3790,f117])).

fof(f117,plain,(
    ! [X8] :
      ( v3_pre_topc(X8,sK0)
      | ~ r2_hidden(X8,u1_pre_topc(sK0))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f75,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f3790,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f3778,f3768])).

fof(f3778,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3770,f115])).

fof(f115,plain,(
    ! [X6] :
      ( v4_pre_topc(X6,sK0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X6),sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f75,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3770,plain,(
    ~ v4_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(resolution,[],[f3767,f142])).

fof(f142,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v4_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f122,f75])).

fof(f122,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
