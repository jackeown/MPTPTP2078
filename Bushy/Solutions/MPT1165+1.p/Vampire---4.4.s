%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t68_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 550 expanded)
%              Number of leaves         :   40 ( 204 expanded)
%              Depth                    :   17
%              Number of atoms          :  748 (4347 expanded)
%              Number of equality atoms :  116 ( 929 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f193,f200,f238,f275,f277,f279,f281,f336,f488,f490,f984,f988,f1071,f1081,f1779,f3152,f3651,f4022,f4378,f5339,f5614])).

fof(f5614,plain,
    ( ~ spl11_1
    | spl11_90 ),
    inference(avatar_split_clause,[],[f5613,f645,f198])).

fof(f198,plain,
    ( spl11_1
  <=> ~ m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f645,plain,
    ( spl11_90
  <=> k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f5613,plain,
    ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(global_subsumption,[],[f122,f5599])).

fof(f5599,plain,
    ( k1_xboole_0 = sK1
    | k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(resolution,[],[f296,f121])).

fof(f121,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,
    ( ( ( k1_xboole_0 = sK1
        & ~ m1_orders_2(sK1,sK0,sK1) )
      | ( m1_orders_2(sK1,sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f89,f88])).

fof(f88,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK0,X1) )
            | ( m1_orders_2(X1,sK0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k1_xboole_0 = sK1
            & ~ m1_orders_2(sK1,X0,sK1) )
          | ( m1_orders_2(sK1,X0,sK1)
            & k1_xboole_0 != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t68_orders_2)).

fof(f296,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X3
      | k3_orders_2(sK0,X3,sK2(sK0,X3,sK1)) = sK1
      | ~ m1_orders_2(sK1,sK0,X3) ) ),
    inference(global_subsumption,[],[f116,f117,f118,f119,f120,f285])).

fof(f285,plain,(
    ! [X3] :
      ( ~ m1_orders_2(sK1,sK0,X3)
      | k1_xboole_0 = X3
      | k3_orders_2(sK0,X3,sK2(sK0,X3,sK1)) = sK1
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f121,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
                        & r2_hidden(sK2(X0,X1,X2),X1)
                        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f92,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',d15_orders_2)).

fof(f120,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f119,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f118,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f117,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f116,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f122,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f90])).

fof(f5339,plain,
    ( ~ spl11_1
    | spl11_82 ),
    inference(avatar_split_clause,[],[f5338,f611,f198])).

fof(f611,plain,
    ( spl11_82
  <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f5338,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(global_subsumption,[],[f122,f5324])).

fof(f5324,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(resolution,[],[f294,f121])).

fof(f294,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0))
      | ~ m1_orders_2(sK1,sK0,X1) ) ),
    inference(global_subsumption,[],[f116,f117,f118,f119,f120,f283])).

fof(f283,plain,(
    ! [X1] :
      ( ~ m1_orders_2(sK1,sK0,X1)
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f121,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f4378,plain,
    ( ~ spl11_1
    | spl11_80 ),
    inference(avatar_split_clause,[],[f4377,f598,f198])).

fof(f598,plain,
    ( spl11_80
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f4377,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(global_subsumption,[],[f122,f4363])).

fof(f4363,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(resolution,[],[f295,f121])).

fof(f295,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | r2_hidden(sK2(sK0,X2,sK1),X2)
      | ~ m1_orders_2(sK1,sK0,X2) ) ),
    inference(global_subsumption,[],[f116,f117,f118,f119,f120,f284])).

fof(f284,plain,(
    ! [X2] :
      ( ~ m1_orders_2(sK1,sK0,X2)
      | k1_xboole_0 = X2
      | r2_hidden(sK2(sK0,X2,sK1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f121,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f4022,plain,
    ( ~ spl11_301
    | spl11_38
    | ~ spl11_82
    | ~ spl11_90
    | ~ spl11_92
    | spl11_131 ),
    inference(avatar_split_clause,[],[f4020,f913,f656,f645,f611,f313,f3145])).

fof(f3145,plain,
    ( spl11_301
  <=> ~ m1_subset_1(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_301])])).

fof(f313,plain,
    ( spl11_38
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f656,plain,
    ( spl11_92
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f913,plain,
    ( spl11_131
  <=> ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k1_tarski(sK2(sK0,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_131])])).

fof(f4020,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),sK1)
    | ~ spl11_82
    | ~ spl11_90
    | ~ spl11_92
    | ~ spl11_131 ),
    inference(resolution,[],[f4009,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t2_subset)).

fof(f4009,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ spl11_82
    | ~ spl11_90
    | ~ spl11_92
    | ~ spl11_131 ),
    inference(resolution,[],[f2121,f914])).

fof(f914,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k1_tarski(sK2(sK0,sK1,sK1))))
    | ~ spl11_131 ),
    inference(avatar_component_clause,[],[f913])).

fof(f2121,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2(sK0,sK1,sK1))))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl11_82
    | ~ spl11_90
    | ~ spl11_92 ),
    inference(superposition,[],[f184,f2103])).

fof(f2103,plain,
    ( k3_xboole_0(sK1,k2_orders_2(sK0,k1_tarski(sK2(sK0,sK1,sK1)))) = sK1
    | ~ spl11_82
    | ~ spl11_90
    | ~ spl11_92 ),
    inference(forward_demodulation,[],[f1778,f657])).

fof(f657,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1))
    | ~ spl11_92 ),
    inference(avatar_component_clause,[],[f656])).

fof(f1778,plain,
    ( k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)))) = sK1
    | ~ spl11_82
    | ~ spl11_90 ),
    inference(forward_demodulation,[],[f1776,f646])).

fof(f646,plain,
    ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) = sK1
    | ~ spl11_90 ),
    inference(avatar_component_clause,[],[f645])).

fof(f1776,plain,
    ( k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)))) = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl11_82 ),
    inference(resolution,[],[f612,f620])).

fof(f620,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k3_xboole_0(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X4))) = k3_orders_2(sK0,sK1,X4) ) ),
    inference(forward_demodulation,[],[f619,f141])).

fof(f141,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',commutativity_k3_xboole_0)).

fof(f619,plain,(
    ! [X4] :
      ( k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X4)),sK1) = k3_orders_2(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f297,f290])).

fof(f290,plain,(
    ! [X8] : k3_xboole_0(X8,sK1) = k9_subset_1(u1_struct_0(sK0),X8,sK1) ),
    inference(resolution,[],[f121,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',redefinition_k9_subset_1)).

fof(f297,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X4)),sK1) = k3_orders_2(sK0,sK1,X4) ) ),
    inference(global_subsumption,[],[f116,f117,f118,f119,f120,f286])).

fof(f286,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X4)),sK1) = k3_orders_2(sK0,sK1,X4)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f121,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',d14_orders_2)).

fof(f612,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl11_82 ),
    inference(avatar_component_clause,[],[f611])).

fof(f184,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f109,f110])).

fof(f110,plain,(
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

fof(f109,plain,(
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
    inference(rectify,[],[f108])).

fof(f108,plain,(
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
    inference(flattening,[],[f107])).

fof(f107,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',d4_xboole_0)).

fof(f3651,plain,
    ( spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_83
    | ~ spl11_131
    | ~ spl11_92 ),
    inference(avatar_split_clause,[],[f3649,f656,f913,f906,f229,f226,f223,f220,f217])).

fof(f217,plain,
    ( spl11_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f220,plain,
    ( spl11_7
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f223,plain,
    ( spl11_9
  <=> ~ v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f226,plain,
    ( spl11_11
  <=> ~ v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f229,plain,
    ( spl11_13
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f906,plain,
    ( spl11_83
  <=> ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f3649,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k2_orders_2(sK0,k1_tarski(sK2(sK0,sK1,sK1))))
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_92 ),
    inference(superposition,[],[f130,f657])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t50_orders_2)).

fof(f3152,plain,
    ( ~ spl11_80
    | spl11_301 ),
    inference(avatar_contradiction_clause,[],[f3151])).

fof(f3151,plain,
    ( $false
    | ~ spl11_80
    | ~ spl11_301 ),
    inference(subsumption_resolution,[],[f1263,f3146])).

fof(f3146,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),sK1)
    | ~ spl11_301 ),
    inference(avatar_component_clause,[],[f3145])).

fof(f1263,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),sK1)
    | ~ spl11_80 ),
    inference(resolution,[],[f599,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t1_subset)).

fof(f599,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ spl11_80 ),
    inference(avatar_component_clause,[],[f598])).

fof(f1779,plain,
    ( spl11_30
    | spl11_92
    | ~ spl11_82 ),
    inference(avatar_split_clause,[],[f1777,f611,f656,f431])).

fof(f431,plain,
    ( spl11_30
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f1777,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_82 ),
    inference(resolution,[],[f612,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',redefinition_k6_domain_1)).

fof(f1081,plain,(
    ~ spl11_140 ),
    inference(avatar_contradiction_clause,[],[f1080])).

fof(f1080,plain,
    ( $false
    | ~ spl11_140 ),
    inference(resolution,[],[f987,f139])).

fof(f139,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',existence_m1_subset_1)).

fof(f987,plain,
    ( ! [X4] : ~ m1_subset_1(X4,sK1)
    | ~ spl11_140 ),
    inference(avatar_component_clause,[],[f986])).

fof(f986,plain,
    ( spl11_140
  <=> ! [X4] : ~ m1_subset_1(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_140])])).

fof(f1071,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f237,f1060])).

fof(f1060,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f199,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f199,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f237,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl11_16
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f988,plain,
    ( spl11_140
    | spl11_38
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f975,f467,f313,f986])).

fof(f467,plain,
    ( spl11_68
  <=> ! [X5] : ~ r2_hidden(X5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f975,plain,
    ( ! [X4] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl11_68 ),
    inference(resolution,[],[f468,f144])).

fof(f468,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f467])).

fof(f984,plain,
    ( ~ spl11_68
    | ~ spl11_80 ),
    inference(avatar_contradiction_clause,[],[f968])).

fof(f968,plain,
    ( $false
    | ~ spl11_68
    | ~ spl11_80 ),
    inference(subsumption_resolution,[],[f599,f468])).

fof(f490,plain,(
    ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f116,f218])).

fof(f218,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f488,plain,
    ( spl11_68
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f477,f263,f467])).

fof(f263,plain,
    ( spl11_31
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f477,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X5,sK1) ) ),
    inference(resolution,[],[f121,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t5_subset)).

fof(f336,plain,
    ( spl11_3
    | ~ spl11_38 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f196,f321])).

fof(f321,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_38 ),
    inference(resolution,[],[f314,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t68_orders_2.p',t6_boole)).

fof(f314,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f313])).

fof(f196,plain,
    ( k1_xboole_0 != sK1
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl11_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f281,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f120,f230])).

fof(f230,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f229])).

fof(f279,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f119,f227])).

fof(f227,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f226])).

fof(f277,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f118,f224])).

fof(f224,plain,
    ( ~ v4_orders_2(sK0)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f223])).

fof(f275,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f117,f221])).

fof(f221,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f220])).

fof(f238,plain,
    ( spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | spl11_16
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f204,f191,f236,f229,f226,f223,f220,f217])).

fof(f204,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f202,f186])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( m1_orders_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f202,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f121,f192])).

fof(f200,plain,
    ( ~ spl11_3
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f122,f198,f195])).

fof(f193,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f125,f191,f188])).

fof(f188,plain,
    ( spl11_0
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).
%------------------------------------------------------------------------------
