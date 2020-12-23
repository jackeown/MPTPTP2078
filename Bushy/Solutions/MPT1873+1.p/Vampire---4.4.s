%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t41_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:32 EDT 2019

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 679 expanded)
%              Number of leaves         :   30 ( 207 expanded)
%              Depth                    :   24
%              Number of atoms          :  707 (5281 expanded)
%              Number of equality atoms :   73 ( 883 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f162,f169,f173,f384,f1423,f1587,f2614,f2852,f10733,f11515])).

fof(f11515,plain,
    ( spl9_1
    | ~ spl9_8
    | ~ spl9_48
    | ~ spl9_272 ),
    inference(avatar_contradiction_clause,[],[f11514])).

fof(f11514,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_8
    | ~ spl9_48
    | ~ spl9_272 ),
    inference(subsumption_resolution,[],[f11344,f1909])).

fof(f1909,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_272 ),
    inference(avatar_component_clause,[],[f1908])).

fof(f1908,plain,
    ( spl9_272
  <=> m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f11344,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_8
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f11343,f94])).

fof(f94,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( ( ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != sK2
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tex_2(sK1,sK0) )
    & ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f79,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tex_2(X1,sK0) )
          & ( ! [X3] :
                ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X3)) = X3
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),sK1,k2_pre_topc(X0,X2)) != X2
              & r1_tarski(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(sK1,X0) )
        & ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),sK1,k2_pre_topc(X0,X3)) = X3
              | ~ r1_tarski(X3,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tex_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2)) != sK2
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t41_tex_2)).

fof(f11343,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_8
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f11342,f95])).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f80])).

fof(f11342,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_8
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f11341,f599])).

fof(f599,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f598,f93])).

fof(f93,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f598,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f585,f94])).

fof(f585,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_48 ),
    inference(resolution,[],[f383,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',fc1_tops_1)).

fof(f383,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl9_48
  <=> m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f11341,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f11336,f148])).

fof(f148,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_1
  <=> ~ v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f11336,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(trivial_inequality_removal,[],[f11334])).

fof(f11334,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(superposition,[],[f109,f338])).

fof(f338,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1))) = sK3(sK0,sK1)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f322,f195])).

fof(f195,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f194,f94])).

fof(f194,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f178,f148])).

fof(f178,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
                    & v4_pre_topc(sK4(X0,X1,X4),X0)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f82,f84,f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
        & v4_pre_topc(sK4(X0,X1,X4),X0)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',d6_tex_2)).

fof(f322,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1))) = sK3(sK0,sK1)
    | ~ r1_tarski(sK3(sK0,sK1),sK1)
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(resolution,[],[f193,f172])).

fof(f172,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
        | ~ r1_tarski(X3,sK1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl9_8
  <=> ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f193,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f192,f94])).

fof(f192,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f177,f148])).

fof(f177,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f10733,plain,
    ( ~ spl9_0
    | spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(avatar_contradiction_clause,[],[f10732])).

fof(f10732,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(subsumption_resolution,[],[f10731,f161])).

fof(f161,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl9_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f10731,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(subsumption_resolution,[],[f10730,f417])).

fof(f417,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f401,f94])).

fof(f401,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f168,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t48_pre_topc)).

fof(f168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f10730,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(resolution,[],[f10729,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t19_xboole_1)).

fof(f10729,plain,
    ( ~ r1_tarski(sK2,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(subsumption_resolution,[],[f10728,f1199])).

fof(f1199,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)) != sK2
    | ~ spl9_3 ),
    inference(superposition,[],[f782,f114])).

fof(f114,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',commutativity_k3_xboole_0)).

fof(f782,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,sK2),sK1) != sK2
    | ~ spl9_3 ),
    inference(superposition,[],[f154,f764])).

fof(f764,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),sK1,X4) = k3_xboole_0(X4,sK1) ),
    inference(forward_demodulation,[],[f183,f184])).

fof(f184,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK1) = k3_xboole_0(X5,sK1) ),
    inference(resolution,[],[f95,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',redefinition_k9_subset_1)).

fof(f183,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X4) ),
    inference(resolution,[],[f95,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',commutativity_k9_subset_1)).

fof(f154,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != sK2
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_3
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f10728,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)) = sK2
    | ~ r1_tarski(sK2,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(resolution,[],[f10720,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',d10_xboole_0)).

fof(f10720,plain,
    ( r1_tarski(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(forward_demodulation,[],[f10714,f114])).

fof(f10714,plain,
    ( r1_tarski(k3_xboole_0(k2_pre_topc(sK0,sK2),sK1),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_202 ),
    inference(resolution,[],[f2608,f1416])).

fof(f1416,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2))
    | ~ spl9_202 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f1415,plain,
    ( spl9_202
  <=> r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_202])])).

fof(f2608,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4(sK0,sK1,sK2))
        | r1_tarski(k3_xboole_0(X1,sK1),sK2) )
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f128,f1698])).

fof(f1698,plain,
    ( k3_xboole_0(sK4(sK0,sK1,sK2),sK1) = sK2
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f1116,f764])).

fof(f1116,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2)) = sK2
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f1115,f161])).

fof(f1115,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2)) = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f1110,f145])).

fof(f145,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_0
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f1110,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2)) = sK2
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f680,f95])).

fof(f680,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,sK4(sK0,X1,sK2)) = sK2
        | ~ v2_tex_2(X1,sK0)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f665,f94])).

fof(f665,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | k9_subset_1(u1_struct_0(sK0),X1,sK4(sK0,X1,sK2)) = sK2
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f168,f106])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t26_xboole_1)).

fof(f2852,plain,
    ( ~ spl9_48
    | spl9_273 ),
    inference(avatar_contradiction_clause,[],[f2851])).

fof(f2851,plain,
    ( $false
    | ~ spl9_48
    | ~ spl9_273 ),
    inference(subsumption_resolution,[],[f2850,f94])).

fof(f2850,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_48
    | ~ spl9_273 ),
    inference(subsumption_resolution,[],[f2849,f383])).

fof(f2849,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_273 ),
    inference(resolution,[],[f1912,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',dt_k2_pre_topc)).

fof(f1912,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_273 ),
    inference(avatar_component_clause,[],[f1911])).

fof(f1911,plain,
    ( spl9_273
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_273])])).

fof(f2614,plain,
    ( ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | spl9_189 ),
    inference(avatar_contradiction_clause,[],[f2613])).

fof(f2613,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f2612,f1370])).

fof(f1370,plain,
    ( ~ r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | ~ spl9_189 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f1369,plain,
    ( spl9_189
  <=> ~ r1_tarski(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).

fof(f2612,plain,
    ( r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f113,f1698])).

fof(f113,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t17_xboole_1)).

fof(f1587,plain,
    ( ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | spl9_205 ),
    inference(avatar_contradiction_clause,[],[f1586])).

fof(f1586,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_205 ),
    inference(subsumption_resolution,[],[f1585,f94])).

fof(f1585,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_205 ),
    inference(subsumption_resolution,[],[f1584,f95])).

fof(f1584,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_205 ),
    inference(subsumption_resolution,[],[f1583,f145])).

fof(f1583,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_205 ),
    inference(subsumption_resolution,[],[f1582,f168])).

fof(f1582,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_205 ),
    inference(subsumption_resolution,[],[f1581,f161])).

fof(f1581,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_205 ),
    inference(resolution,[],[f1422,f105])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f1422,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl9_205 ),
    inference(avatar_component_clause,[],[f1421])).

fof(f1421,plain,
    ( spl9_205
  <=> ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_205])])).

fof(f1423,plain,
    ( ~ spl9_189
    | spl9_202
    | ~ spl9_205
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1348,f167,f160,f144,f1421,f1415,f1369])).

fof(f1348,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2))
    | ~ r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f1070,f681])).

fof(f681,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X2,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK2),X2)
        | ~ r1_tarski(sK2,X2) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f668,f94])).

fof(f668,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ v4_pre_topc(X2,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f168,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t31_tops_1)).

fof(f1070,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f1069,f161])).

fof(f1069,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f1056,f145])).

fof(f1056,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f679,f95])).

fof(f679,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f664,f94])).

fof(f664,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f168,f104])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f384,plain,
    ( spl9_0
    | spl9_48 ),
    inference(avatar_split_clause,[],[f377,f382,f144])).

fof(f377,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f177,f94])).

fof(f173,plain,
    ( spl9_0
    | spl9_8 ),
    inference(avatar_split_clause,[],[f96,f171,f144])).

fof(f96,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f169,plain,
    ( ~ spl9_1
    | spl9_6 ),
    inference(avatar_split_clause,[],[f97,f167,f147])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f162,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f98,f160,f147])).

fof(f98,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f155,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f99,f153,f147])).

fof(f99,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != sK2
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).
%------------------------------------------------------------------------------
