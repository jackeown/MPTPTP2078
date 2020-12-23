%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t13_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:28 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 347 expanded)
%              Number of leaves         :    6 ( 110 expanded)
%              Depth                    :   21
%              Number of atoms          :  203 (2654 expanded)
%              Number of equality atoms :   31 ( 395 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(subsumption_resolution,[],[f865,f847])).

fof(f847,plain,(
    ~ v1_tex_2(sK1,sK0) ),
    inference(resolution,[],[f159,f231])).

fof(f231,plain,(
    v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f230,f156])).

fof(f156,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,
    ( ( ~ v1_tex_2(sK1,sK0)
      | ~ v1_subset_1(sK2,u1_struct_0(sK0)) )
    & ( v1_tex_2(sK1,sK0)
      | v1_subset_1(sK2,u1_struct_0(sK0)) )
    & u1_struct_0(sK1) = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f115,f118,f117,f116])).

fof(f116,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) )
                & ( v1_tex_2(X1,X0)
                  | v1_subset_1(X2,u1_struct_0(X0)) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,sK0)
                | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
              & ( v1_tex_2(X1,sK0)
                | v1_subset_1(X2,u1_struct_0(sK0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f117,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ( ~ v1_tex_2(sK1,X0)
              | ~ v1_subset_1(X2,u1_struct_0(X0)) )
            & ( v1_tex_2(sK1,X0)
              | v1_subset_1(X2,u1_struct_0(X0)) )
            & u1_struct_0(sK1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v1_tex_2(X1,X0)
            | ~ v1_subset_1(X2,u1_struct_0(X0)) )
          & ( v1_tex_2(X1,X0)
            | v1_subset_1(X2,u1_struct_0(X0)) )
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v1_tex_2(X1,X0)
          | ~ v1_subset_1(sK2,u1_struct_0(X0)) )
        & ( v1_tex_2(X1,X0)
          | v1_subset_1(sK2,u1_struct_0(X0)) )
        & u1_struct_0(X1) = sK2
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f80])).

fof(f80,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v1_subset_1(X2,u1_struct_0(X0))
                  <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t13_tex_2.p',t13_tex_2)).

fof(f230,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f229,f157])).

fof(f157,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f119])).

fof(f229,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f228,f158])).

fof(f158,plain,
    ( v1_tex_2(sK1,sK0)
    | v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f119])).

fof(f228,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(forward_demodulation,[],[f227,f157])).

fof(f227,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f222,f154])).

fof(f154,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f119])).

fof(f222,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f121,f122])).

fof(f122,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t13_tex_2.p',d3_tex_2)).

fof(f155,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f119])).

fof(f159,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f119])).

fof(f865,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f863,f231])).

fof(f863,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK0))
    | v1_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f861,f235])).

fof(f235,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ v1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f225,f154])).

fof(f225,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ v1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f861,plain,(
    sK2 = sK3(sK0,sK1) ),
    inference(forward_demodulation,[],[f860,f157])).

fof(f860,plain,(
    u1_struct_0(sK1) = sK3(sK0,sK1) ),
    inference(subsumption_resolution,[],[f859,f154])).

fof(f859,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f855,f155])).

fof(f855,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f847,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f123])).
%------------------------------------------------------------------------------
