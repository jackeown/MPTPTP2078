%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t41_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:39 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 154 expanded)
%              Number of leaves         :   13 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  281 (1022 expanded)
%              Number of equality atoms :   36 (  38 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(global_subsumption,[],[f315,f324])).

fof(f324,plain,(
    sP1(k1_tops_2(sK2,sK4,sK5),sK5,sK2,sK4) ),
    inference(unit_resulting_resolution,[],[f73,f75,f76,f200,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X3,X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f43,f53,f52])).

fof(f52,plain,(
    ! [X1,X0,X2,X3] :
      ( sP0(X1,X0,X2,X3)
    <=> ! [X4] :
          ( ( r2_hidden(X4,X3)
          <=> ? [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                & r2_hidden(X5,X2)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f53,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP0(X1,X0,X2,X3) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t41_tops_2.p',d3_tops_2)).

fof(f200,plain,(
    m1_subset_1(k1_tops_2(sK2,sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))) ),
    inference(unit_resulting_resolution,[],[f73,f75,f76,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t41_tops_2.p',dt_k1_tops_2)).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_tops_2(sK2,sK4,sK5))
    & r2_hidden(sK3,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f40,f58,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_tops_2(sK2,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3,X2),k1_tops_2(X0,X2,X3))
                & r2_hidden(sK3,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
              & r2_hidden(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK4),k1_tops_2(X0,sK4,X3))
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,sK5))
        & r2_hidden(X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t41_tops_2.p',t41_tops_2)).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f315,plain,(
    ~ sP1(k1_tops_2(sK2,sK4,sK5),sK5,sK2,sK4) ),
    inference(unit_resulting_resolution,[],[f299,f101])).

fof(f101,plain,(
    ! [X2,X3,X1] :
      ( ~ sP1(k1_tops_2(X2,X3,X1),X1,X2,X3)
      | sP0(X3,X2,X1,k1_tops_2(X2,X3,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k1_tops_2(X2,X3,X1) != X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X2,X3,X1) = X0
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k1_tops_2(X2,X3,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP0(X1,X0,X2,X3) )
        & ( sP0(X1,X0,X2,X3)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f299,plain,(
    ~ sP0(sK4,sK2,sK5,k1_tops_2(sK2,sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f77,f74,f78,f148,f102])).

fof(f102,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X8,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X8,X0),X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X1),X8,X0) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK6(X0,X1,X2,X3)
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2,X3),X0) = sK6(X0,X1,X2,X3)
              & r2_hidden(sK7(X0,X1,X2,X3),X2)
              & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ( k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2,X7),X0) = X7
                  & r2_hidden(sK8(X0,X1,X2,X7),X2)
                  & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK6(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X1),X6,X0) = sK6(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2,X3),X0) = X4
        & r2_hidden(sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK8(X0,X1,X2,X7),X0) = X7
        & r2_hidden(sK8(X0,X1,X2,X7),X2)
        & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                  & r2_hidden(X6,X2)
                  & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ? [X9] :
                    ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
                    & r2_hidden(X9,X2)
                    & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f148,plain,(
    m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
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
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t41_tops_2.p',t38_tops_2)).

fof(f78,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_tops_2(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f59])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f77,plain,(
    r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
