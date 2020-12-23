%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1407+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:53 EST 2020

% Result     : Theorem 17.62s
% Output     : Refutation 17.62s
% Verified   : 
% Statistics : Number of formulae       :  297 (1373 expanded)
%              Number of leaves         :   46 ( 512 expanded)
%              Depth                    :   15
%              Number of atoms          : 1269 (14438 expanded)
%              Number of equality atoms :   16 ( 203 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f235,f287,f329,f345,f389,f401,f428,f433,f435,f700,f727,f737,f850,f855,f856,f859,f5410,f5897,f5944,f5994,f26938,f26952,f27067,f27090,f27177,f27187,f27379,f27402,f29891,f30012,f30032])).

fof(f30032,plain,
    ( ~ spl9_38
    | spl9_82 ),
    inference(avatar_contradiction_clause,[],[f30031])).

fof(f30031,plain,
    ( $false
    | ~ spl9_38
    | spl9_82 ),
    inference(subsumption_resolution,[],[f27146,f3674])).

fof(f3674,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | spl9_82 ),
    inference(avatar_component_clause,[],[f3672])).

fof(f3672,plain,
    ( spl9_82
  <=> r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f27146,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_38 ),
    inference(resolution,[],[f27099,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f27099,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f854,f368])).

fof(f368,plain,(
    ! [X6] : k9_subset_1(u1_struct_0(sK2),X6,sK4) = k3_xboole_0(X6,sK4) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
      | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
      | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & v20_lattices(sK4,sK2)
    & v19_lattices(sK4,sK2)
    & ~ v1_xboole_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v20_lattices(sK3,sK2)
    & v19_lattices(sK3,sK2)
    & ~ v1_xboole_0(sK3)
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  | ~ v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  | v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X2,X0)
                & v19_lattices(X2,X0)
                & ~ v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(sK2)))
                | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2)
                | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2)
                | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),X1,X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
              & v20_lattices(X2,sK2)
              & v19_lattices(X2,sK2)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v20_lattices(X1,sK2)
          & v19_lattices(X1,sK2)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(sK2)))
              | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2)
              | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2)
              | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),X1,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
            & v20_lattices(X2,sK2)
            & v19_lattices(X2,sK2)
            & ~ v1_xboole_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v20_lattices(X1,sK2)
        & v19_lattices(X1,sK2)
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,X2),k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,X2),sK2)
            | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,X2),sK2)
            | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
          & v20_lattices(X2,sK2)
          & v19_lattices(X2,sK2)
          & ~ v1_xboole_0(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v20_lattices(sK3,sK2)
      & v19_lattices(sK3,sK2)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,X2),k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,X2),sK2)
          | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,X2),sK2)
          | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        & v20_lattices(X2,sK2)
        & v19_lattices(X2,sK2)
        & ~ v1_xboole_0(X2) )
   => ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
        | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
        | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      & v20_lattices(sK4,sK2)
      & v19_lattices(sK4,sK2)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X2,X0)
              & v19_lattices(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X2,X0)
              & v19_lattices(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v20_lattices(X2,X0)
                  & v19_lattices(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & ~ v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X2,X0)
                & v19_lattices(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ~ v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_filter_1)).

fof(f854,plain,
    ( r2_hidden(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl9_38
  <=> r2_hidden(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f30012,plain,
    ( ~ spl9_21
    | ~ spl9_36
    | ~ spl9_82
    | spl9_435 ),
    inference(avatar_contradiction_clause,[],[f30011])).

fof(f30011,plain,
    ( $false
    | ~ spl9_21
    | ~ spl9_36
    | ~ spl9_82
    | spl9_435 ),
    inference(subsumption_resolution,[],[f29977,f27268])).

fof(f27268,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_36 ),
    inference(resolution,[],[f27189,f90])).

fof(f27189,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f845,f368])).

fof(f845,plain,
    ( r2_hidden(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl9_36
  <=> r2_hidden(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f29977,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_21
    | ~ spl9_82
    | spl9_435 ),
    inference(subsumption_resolution,[],[f29967,f3673])).

fof(f3673,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f3672])).

fof(f29967,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_21
    | spl9_435 ),
    inference(resolution,[],[f27378,f10104])).

fof(f10104,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK4)
        | ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f10103,f366])).

fof(f366,plain,(
    ! [X4] :
      ( m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_hidden(X4,sK4) ) ),
    inference(resolution,[],[f58,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f10103,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK4)
        | ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f415,f366])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK4)
        | ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_21 ),
    inference(resolution,[],[f276,f70])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_lattices(X1,X4,X5),X0)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X0) )
          & ( r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
            | ( r2_hidden(sK7(X0,X1),X0)
              & r2_hidden(sK6(X0,X1),X0) ) )
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ( ( ( r2_hidden(X5,X0)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_lattices(X1,X4,X5),X0) )
                  & ( r2_hidden(k4_lattices(X1,X4,X5),X0)
                    | ~ r2_hidden(X5,X0)
                    | ~ r2_hidden(X4,X0) ) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_hidden(k4_lattices(X1,X2,X3),X0)
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
              & ( r2_hidden(k4_lattices(X1,X2,X3),X0)
                | ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X0) ) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ( ~ r2_hidden(k4_lattices(X1,sK6(X0,X1),X3),X0)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK6(X0,X1),X0) )
            & ( r2_hidden(k4_lattices(X1,sK6(X0,X1),X3),X0)
              | ( r2_hidden(X3,X0)
                & r2_hidden(sK6(X0,X1),X0) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_lattices(X1,sK6(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(sK6(X0,X1),X0) )
          & ( r2_hidden(k4_lattices(X1,sK6(X0,X1),X3),X0)
            | ( r2_hidden(X3,X0)
              & r2_hidden(sK6(X0,X1),X0) ) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ~ r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
          | ( r2_hidden(sK7(X0,X1),X0)
            & r2_hidden(sK6(X0,X1),X0) ) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(k4_lattices(X1,X2,X3),X0)
                  | ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X0) )
                & ( r2_hidden(k4_lattices(X1,X2,X3),X0)
                  | ( r2_hidden(X3,X0)
                    & r2_hidden(X2,X0) ) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ( ( ( r2_hidden(X5,X0)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_lattices(X1,X4,X5),X0) )
                  & ( r2_hidden(k4_lattices(X1,X4,X5),X0)
                    | ~ r2_hidden(X5,X0)
                    | ~ r2_hidden(X4,X0) ) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                  | ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X2,X1) )
                & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                  | ( r2_hidden(X3,X1)
                    & r2_hidden(X2,X1) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ( ( ( r2_hidden(X3,X1)
                      & r2_hidden(X2,X1) )
                    | ~ r2_hidden(k4_lattices(X0,X2,X3),X1) )
                  & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                  | ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X2,X1) )
                & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                  | ( r2_hidden(X3,X1)
                    & r2_hidden(X2,X1) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ( ( ( r2_hidden(X3,X1)
                      & r2_hidden(X2,X1) )
                    | ~ r2_hidden(k4_lattices(X0,X2,X3),X1) )
                  & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  & r2_hidden(X2,X1) )
              <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f276,plain,
    ( sP0(sK4,sK2)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl9_21
  <=> sP0(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f27378,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK4)
    | spl9_435 ),
    inference(avatar_component_clause,[],[f27376])).

fof(f27376,plain,
    ( spl9_435
  <=> r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_435])])).

fof(f29891,plain,
    ( ~ spl9_15
    | ~ spl9_36
    | ~ spl9_81
    | spl9_434 ),
    inference(avatar_contradiction_clause,[],[f29890])).

fof(f29890,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_36
    | ~ spl9_81
    | spl9_434 ),
    inference(subsumption_resolution,[],[f29856,f27267])).

fof(f27267,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ spl9_36 ),
    inference(resolution,[],[f27189,f91])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f29856,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ spl9_15
    | ~ spl9_81
    | spl9_434 ),
    inference(subsumption_resolution,[],[f29846,f3669])).

fof(f3669,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f3668])).

fof(f3668,plain,
    ( spl9_81
  <=> r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f29846,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ spl9_15
    | spl9_434 ),
    inference(resolution,[],[f27374,f10020])).

fof(f10020,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK3)
        | ~ r2_hidden(X1,sK3)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f10019,f306])).

fof(f306,plain,(
    ! [X4] :
      ( m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_hidden(X4,sK3) ) ),
    inference(resolution,[],[f54,f62])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f10019,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK3)
        | ~ r2_hidden(X1,sK3)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f359,f306])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_lattices(sK2,X0,X1),sK3)
        | ~ r2_hidden(X1,sK3)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_15 ),
    inference(resolution,[],[f213,f70])).

fof(f213,plain,
    ( sP0(sK3,sK2)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl9_15
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f27374,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK3)
    | spl9_434 ),
    inference(avatar_component_clause,[],[f27372])).

fof(f27372,plain,
    ( spl9_434
  <=> r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_434])])).

fof(f27402,plain,
    ( spl9_33
    | ~ spl9_36 ),
    inference(avatar_contradiction_clause,[],[f27401])).

fof(f27401,plain,
    ( $false
    | spl9_33
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f753,f27189])).

fof(f753,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | spl9_33 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl9_33
  <=> r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f27379,plain,
    ( ~ spl9_434
    | ~ spl9_435
    | spl9_37 ),
    inference(avatar_split_clause,[],[f27359,f847,f27376,f27372])).

fof(f847,plain,
    ( spl9_37
  <=> r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f27359,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK4)
    | ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK3)
    | spl9_37 ),
    inference(resolution,[],[f27188,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f27188,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4))
    | spl9_37 ),
    inference(forward_demodulation,[],[f848,f368])).

fof(f848,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_37 ),
    inference(avatar_component_clause,[],[f847])).

fof(f27187,plain,
    ( ~ spl9_33
    | ~ spl9_34
    | spl9_26
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f27186,f852,f425,f756,f752])).

fof(f756,plain,
    ( spl9_34
  <=> r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f425,plain,
    ( spl9_26
  <=> sP0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f27186,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | spl9_26
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f6109,f27099])).

fof(f6109,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | spl9_26 ),
    inference(resolution,[],[f3460,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X0)
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3460,plain,
    ( ~ sP0(k3_xboole_0(sK3,sK4),sK2)
    | spl9_26 ),
    inference(forward_demodulation,[],[f427,f368])).

fof(f427,plain,
    ( ~ sP0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f425])).

fof(f27177,plain,
    ( ~ spl9_15
    | spl9_26
    | spl9_36
    | ~ spl9_37
    | ~ spl9_432 ),
    inference(avatar_contradiction_clause,[],[f27176])).

fof(f27176,plain,
    ( $false
    | ~ spl9_15
    | spl9_26
    | spl9_36
    | ~ spl9_37
    | ~ spl9_432 ),
    inference(subsumption_resolution,[],[f27175,f26900])).

fof(f26900,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ spl9_15
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f26899,f3459])).

fof(f3459,plain,
    ( m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | spl9_26 ),
    inference(forward_demodulation,[],[f835,f368])).

fof(f835,plain,
    ( m1_subset_1(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),u1_struct_0(sK2))
    | spl9_26 ),
    inference(resolution,[],[f427,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f26899,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ spl9_15
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f26869,f3458])).

fof(f3458,plain,
    ( m1_subset_1(sK7(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | spl9_26 ),
    inference(forward_demodulation,[],[f836,f368])).

fof(f836,plain,
    ( m1_subset_1(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),u1_struct_0(sK2))
    | spl9_26 ),
    inference(resolution,[],[f427,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK7(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f26869,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ m1_subset_1(sK7(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ spl9_15
    | ~ spl9_37 ),
    inference(resolution,[],[f5167,f360])).

fof(f360,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_lattices(sK2,X2,X3),sK3)
        | r2_hidden(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    | ~ spl9_15 ),
    inference(resolution,[],[f213,f71])).

fof(f71,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_lattices(X1,X4,X5),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5167,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK3)
    | ~ spl9_37 ),
    inference(resolution,[],[f3438,f91])).

fof(f3438,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4))
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f849,f368])).

fof(f849,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f847])).

fof(f27175,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | spl9_36
    | ~ spl9_432 ),
    inference(subsumption_resolution,[],[f27165,f26933])).

fof(f26933,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_432 ),
    inference(avatar_component_clause,[],[f26932])).

fof(f26932,plain,
    ( spl9_432
  <=> r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_432])])).

fof(f27165,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK3)
    | spl9_36 ),
    inference(resolution,[],[f27100,f89])).

fof(f27100,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | spl9_36 ),
    inference(forward_demodulation,[],[f844,f368])).

fof(f844,plain,
    ( ~ r2_hidden(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_36 ),
    inference(avatar_component_clause,[],[f843])).

fof(f27090,plain,
    ( ~ spl9_82
    | spl9_432
    | ~ spl9_21
    | spl9_26
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f27089,f847,f425,f274,f26932,f3672])).

fof(f27089,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_21
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f27088,f276])).

fof(f27088,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ sP0(sK4,sK2)
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f27022,f3459])).

fof(f27022,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ sP0(sK4,sK2)
    | ~ spl9_37 ),
    inference(resolution,[],[f5168,f595])).

fof(f595,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(k4_lattices(sK2,X7,X6),X8)
      | r2_hidden(X7,X8)
      | ~ r2_hidden(X6,sK4)
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ sP0(X8,sK2) ) ),
    inference(resolution,[],[f366,f71])).

fof(f5168,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),sK4)
    | ~ spl9_37 ),
    inference(resolution,[],[f3438,f90])).

fof(f27067,plain,
    ( ~ spl9_21
    | spl9_26
    | ~ spl9_37
    | spl9_82 ),
    inference(avatar_contradiction_clause,[],[f27066])).

fof(f27066,plain,
    ( $false
    | ~ spl9_21
    | spl9_26
    | ~ spl9_37
    | spl9_82 ),
    inference(subsumption_resolution,[],[f27065,f276])).

fof(f27065,plain,
    ( ~ sP0(sK4,sK2)
    | spl9_26
    | ~ spl9_37
    | spl9_82 ),
    inference(subsumption_resolution,[],[f27064,f3459])).

fof(f27064,plain,
    ( ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ sP0(sK4,sK2)
    | spl9_26
    | ~ spl9_37
    | spl9_82 ),
    inference(subsumption_resolution,[],[f27063,f3458])).

fof(f27063,plain,
    ( ~ m1_subset_1(sK7(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ sP0(sK4,sK2)
    | ~ spl9_37
    | spl9_82 ),
    inference(subsumption_resolution,[],[f27027,f3674])).

fof(f27027,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ m1_subset_1(sK7(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ sP0(sK4,sK2)
    | ~ spl9_37 ),
    inference(resolution,[],[f5168,f72])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r2_hidden(k4_lattices(X1,X4,X5),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f26952,plain,
    ( ~ spl9_81
    | ~ spl9_82
    | spl9_38 ),
    inference(avatar_split_clause,[],[f6634,f852,f3672,f3668])).

fof(f6634,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | spl9_38 ),
    inference(resolution,[],[f3437,f89])).

fof(f3437,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,sK4))
    | spl9_38 ),
    inference(forward_demodulation,[],[f853,f368])).

fof(f853,plain,
    ( ~ r2_hidden(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_38 ),
    inference(avatar_component_clause,[],[f852])).

fof(f26938,plain,
    ( ~ spl9_82
    | spl9_81
    | ~ spl9_15
    | spl9_26
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f26937,f847,f425,f211,f3668,f3672])).

fof(f26937,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ spl9_15
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f26936,f213])).

fof(f26936,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ sP0(sK3,sK2)
    | spl9_26
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f26888,f3459])).

fof(f26888,plain,
    ( r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK4)
    | ~ m1_subset_1(sK6(k3_xboole_0(sK3,sK4),sK2),u1_struct_0(sK2))
    | ~ sP0(sK3,sK2)
    | ~ spl9_37 ),
    inference(resolution,[],[f5167,f597])).

fof(f597,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(k4_lattices(sK2,X14,X12),X13)
      | r2_hidden(X12,X13)
      | ~ r2_hidden(X12,sK4)
      | ~ m1_subset_1(X14,u1_struct_0(sK2))
      | ~ sP0(X13,sK2) ) ),
    inference(resolution,[],[f366,f72])).

fof(f5994,plain,(
    ~ spl9_103 ),
    inference(avatar_contradiction_clause,[],[f5953])).

fof(f5953,plain,
    ( $false
    | ~ spl9_103 ),
    inference(resolution,[],[f5891,f498])).

fof(f498,plain,(
    r2_hidden(sK5(sK3),sK3) ),
    inference(resolution,[],[f166,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f166,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,sK3)
      | r2_hidden(X8,sK3) ) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f5891,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK3)
    | ~ spl9_103 ),
    inference(avatar_component_clause,[],[f5890])).

fof(f5890,plain,
    ( spl9_103
  <=> ! [X2] : ~ r2_hidden(X2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f5944,plain,(
    ~ spl9_104 ),
    inference(avatar_contradiction_clause,[],[f5903])).

fof(f5903,plain,
    ( $false
    | ~ spl9_104 ),
    inference(resolution,[],[f5894,f510])).

fof(f510,plain,(
    r2_hidden(sK5(sK4),sK4) ),
    inference(resolution,[],[f173,f64])).

fof(f173,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,sK4)
      | r2_hidden(X8,sK4) ) ),
    inference(resolution,[],[f55,f63])).

fof(f55,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f5894,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK4)
    | ~ spl9_104 ),
    inference(avatar_component_clause,[],[f5893])).

fof(f5893,plain,
    ( spl9_104
  <=> ! [X3] : ~ r2_hidden(X3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f5897,plain,
    ( spl9_103
    | spl9_104
    | ~ spl9_1
    | ~ spl9_13
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f5896,f256,f202,f93,f5893,f5890])).

fof(f93,plain,
    ( spl9_1
  <=> v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f202,plain,
    ( spl9_13
  <=> ! [X3,X2] :
        ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ r2_hidden(X3,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f256,plain,
    ( spl9_18
  <=> ! [X1,X0] :
        ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f5896,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK4)
        | ~ r2_hidden(X5,sK3) )
    | ~ spl9_1
    | ~ spl9_13
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f5858,f1229])).

fof(f1229,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k3_lattices(sK2,X0,X1),sK3)
        | ~ r2_hidden(X1,sK3)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl9_13 ),
    inference(resolution,[],[f203,f366])).

fof(f203,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r2_hidden(k3_lattices(sK2,X2,X3),sK3)
        | ~ r2_hidden(X3,sK3) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f5858,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k3_lattices(sK2,X4,X5),sK3)
        | ~ r2_hidden(X4,sK4)
        | ~ r2_hidden(X5,sK3) )
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(resolution,[],[f5455,f1236])).

fof(f1236,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k3_lattices(sK2,X2,X3),sK4)
        | ~ r2_hidden(X2,sK4)
        | ~ r2_hidden(X3,sK3) )
    | ~ spl9_18 ),
    inference(resolution,[],[f257,f306])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(k3_lattices(sK2,X0,X1),sK4)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f5455,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl9_1 ),
    inference(resolution,[],[f5374,f89])).

fof(f5374,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK3,sK4))
    | ~ spl9_1 ),
    inference(resolution,[],[f5373,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f5373,plain,
    ( v1_xboole_0(k3_xboole_0(sK3,sK4))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f95,f368])).

fof(f95,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f5410,plain,
    ( spl9_34
    | spl9_28
    | spl9_81 ),
    inference(avatar_split_clause,[],[f4377,f3668,f445,f756])).

fof(f445,plain,
    ( spl9_28
  <=> sP0(k3_xboole_0(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f4377,plain,
    ( sP0(k3_xboole_0(sK3,sK4),sK2)
    | r2_hidden(k4_lattices(sK2,sK6(k3_xboole_0(sK3,sK4),sK2),sK7(k3_xboole_0(sK3,sK4),sK2)),k3_xboole_0(sK3,sK4))
    | spl9_81 ),
    inference(resolution,[],[f3682,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3682,plain,
    ( ! [X0] : ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),k3_xboole_0(sK3,X0))
    | spl9_81 ),
    inference(resolution,[],[f3670,f91])).

fof(f3670,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(sK3,sK4),sK2),sK3)
    | spl9_81 ),
    inference(avatar_component_clause,[],[f3668])).

fof(f859,plain,
    ( spl9_26
    | ~ spl9_28 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | spl9_26
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f857,f58])).

fof(f857,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_26
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f841,f446])).

fof(f446,plain,
    ( sP0(k3_xboole_0(sK3,sK4),sK2)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f445])).

fof(f841,plain,
    ( ~ sP0(k3_xboole_0(sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_26 ),
    inference(superposition,[],[f427,f60])).

fof(f856,plain,
    ( ~ spl9_36
    | ~ spl9_38
    | ~ spl9_37
    | spl9_26 ),
    inference(avatar_split_clause,[],[f839,f425,f847,f852,f843])).

fof(f839,plain,
    ( ~ r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ r2_hidden(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ r2_hidden(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_26 ),
    inference(resolution,[],[f427,f77])).

fof(f855,plain,
    ( spl9_38
    | spl9_37
    | spl9_26 ),
    inference(avatar_split_clause,[],[f838,f425,f847,f852])).

fof(f838,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r2_hidden(sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_26 ),
    inference(resolution,[],[f427,f76])).

fof(f850,plain,
    ( spl9_36
    | spl9_37
    | spl9_26 ),
    inference(avatar_split_clause,[],[f837,f425,f847,f843])).

fof(f837,plain,
    ( r2_hidden(k4_lattices(sK2,sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),sK7(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r2_hidden(sK6(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_26 ),
    inference(resolution,[],[f427,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(k4_lattices(X1,sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f737,plain,
    ( ~ spl9_26
    | spl9_3
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f732,f421,f101,f425])).

fof(f101,plain,
    ( spl9_3
  <=> v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f421,plain,
    ( spl9_25
  <=> sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f732,plain,
    ( v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ sP0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ spl9_25 ),
    inference(resolution,[],[f422,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v20_lattices(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f422,plain,
    ( sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f421])).

fof(f727,plain,
    ( spl9_1
    | spl9_25
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f726,f105,f421,f93])).

fof(f105,plain,
    ( spl9_4
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f726,plain,
    ( sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f725,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f725,plain,
    ( sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f724,f49])).

fof(f49,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f724,plain,
    ( sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f717,f50])).

fof(f50,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f717,plain,
    ( sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f27,f26])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_0)).

fof(f106,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f700,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f695,f58])).

fof(f695,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_4 ),
    inference(resolution,[],[f107,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f107,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f435,plain,(
    spl9_17 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl9_17 ),
    inference(subsumption_resolution,[],[f254,f58])).

fof(f254,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl9_17
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f433,plain,(
    spl9_11 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl9_11 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl9_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f428,plain,
    ( ~ spl9_25
    | ~ spl9_26
    | spl9_2 ),
    inference(avatar_split_clause,[],[f418,f97,f425,f421])).

fof(f97,plain,
    ( spl9_2
  <=> v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f418,plain,
    ( ~ sP0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ sP1(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | spl9_2 ),
    inference(resolution,[],[f99,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v19_lattices(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,
    ( ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f401,plain,(
    spl9_20 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl9_20 ),
    inference(subsumption_resolution,[],[f399,f48])).

fof(f399,plain,
    ( v2_struct_0(sK2)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f398,f49])).

fof(f398,plain,
    ( ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f397,f50])).

fof(f397,plain,
    ( ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f396,f55])).

fof(f396,plain,
    ( v1_xboole_0(sK4)
    | ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f395,f58])).

fof(f395,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK4)
    | ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_20 ),
    inference(resolution,[],[f272,f78])).

fof(f272,plain,
    ( ~ sP1(sK2,sK4)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl9_20
  <=> sP1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f389,plain,
    ( ~ spl9_20
    | spl9_21 ),
    inference(avatar_split_clause,[],[f388,f274,f270])).

fof(f388,plain,
    ( sP0(sK4,sK2)
    | ~ sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f387,f55])).

fof(f387,plain,
    ( sP0(sK4,sK2)
    | v1_xboole_0(sK4)
    | ~ sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f386,f56])).

fof(f56,plain,(
    v19_lattices(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f386,plain,
    ( sP0(sK4,sK2)
    | ~ v19_lattices(sK4,sK2)
    | v1_xboole_0(sK4)
    | ~ sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f365,f57])).

fof(f57,plain,(
    v20_lattices(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f365,plain,
    ( sP0(sK4,sK2)
    | ~ v20_lattices(sK4,sK2)
    | ~ v19_lattices(sK4,sK2)
    | v1_xboole_0(sK4)
    | ~ sP1(sK2,sK4) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f345,plain,(
    spl9_14 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl9_14 ),
    inference(subsumption_resolution,[],[f343,f48])).

fof(f343,plain,
    ( v2_struct_0(sK2)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f342,f49])).

fof(f342,plain,
    ( ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f341,f50])).

fof(f341,plain,
    ( ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f340,f51])).

fof(f340,plain,
    ( v1_xboole_0(sK3)
    | ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f339,f54])).

fof(f339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | ~ l3_lattices(sK2)
    | ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | spl9_14 ),
    inference(resolution,[],[f209,f78])).

fof(f209,plain,
    ( ~ sP1(sK2,sK3)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl9_14
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f329,plain,
    ( ~ spl9_14
    | spl9_15 ),
    inference(avatar_split_clause,[],[f328,f211,f207])).

fof(f328,plain,
    ( sP0(sK3,sK2)
    | ~ sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f327,f51])).

fof(f327,plain,
    ( sP0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f326,f52])).

fof(f52,plain,(
    v19_lattices(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f326,plain,
    ( sP0(sK3,sK2)
    | ~ v19_lattices(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f305,f53])).

fof(f53,plain,(
    v20_lattices(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f305,plain,
    ( sP0(sK3,sK2)
    | ~ v20_lattices(sK3,sK2)
    | ~ v19_lattices(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ sP1(sK2,sK3) ),
    inference(resolution,[],[f54,f65])).

fof(f287,plain,
    ( ~ spl9_17
    | spl9_18 ),
    inference(avatar_split_clause,[],[f286,f256,f252])).

fof(f286,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f285,f62])).

fof(f285,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f284,f48])).

fof(f284,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f283,f49])).

fof(f283,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f282,f50])).

fof(f282,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f281,f55])).

fof(f281,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f278,f56])).

fof(f278,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_lattices(sK2,X0,X1),sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v19_lattices(sK4,sK2)
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_lattices(X0,X1,X2),X3)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X3,X0)
      | ~ v19_lattices(X3,X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                    & r2_hidden(k3_lattices(X0,X1,X2),X3) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v20_lattices(X3,X0)
                  | ~ v19_lattices(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                    & r2_hidden(k3_lattices(X0,X1,X2),X3) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v20_lattices(X3,X0)
                  | ~ v19_lattices(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v20_lattices(X3,X0)
                    & v19_lattices(X3,X0)
                    & ~ v1_xboole_0(X3) )
                 => ( r2_hidden(X1,X3)
                   => ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                      & r2_hidden(k3_lattices(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_0)).

fof(f235,plain,
    ( ~ spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f234,f202,f189])).

fof(f234,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f233,f62])).

fof(f233,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f232,f48])).

fof(f232,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f231,f49])).

fof(f231,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f230,f50])).

fof(f230,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f229,f51])).

fof(f229,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f220,f52])).

fof(f220,plain,(
    ! [X2,X3] :
      ( r2_hidden(k3_lattices(sK2,X2,X3),sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v19_lattices(sK3,sK2)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f53,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_lattices(X0,X2,X1),X3)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X3,X0)
      | ~ v19_lattices(X3,X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f59,f105,f101,f97,f93])).

fof(f59,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v20_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v19_lattices(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK2),sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
