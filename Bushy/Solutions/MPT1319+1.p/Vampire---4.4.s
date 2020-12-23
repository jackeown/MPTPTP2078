%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t40_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:39 EDT 2019

% Result     : Theorem 51.70s
% Output     : Refutation 51.70s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 379 expanded)
%              Number of leaves         :    7 (  70 expanded)
%              Depth                    :   27
%              Number of atoms          :  291 (1645 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41536,f72])).

fof(f72,plain,(
    ~ r1_tarski(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',t40_tops_2)).

fof(f41536,plain,(
    r1_tarski(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(resolution,[],[f41531,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',d3_tarski)).

fof(f41531,plain,(
    r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f41530,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41530,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,sK3)) ),
    inference(resolution,[],[f23845,f3661])).

fof(f3661,plain,(
    r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK3) ),
    inference(resolution,[],[f3556,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f71,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f71,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f3556,plain,(
    r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK2) ),
    inference(subsumption_resolution,[],[f986,f825])).

fof(f825,plain,(
    m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f824,f74])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f824,plain,
    ( m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f823,f73])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f823,plain,
    ( m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f506,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_2(sK0,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f75,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',dt_k1_tops_2)).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f506,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_2(sK0,sK1,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),X0) ) ),
    inference(resolution,[],[f157,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',t4_subset)).

fof(f157,plain,(
    r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,sK2)) ),
    inference(resolution,[],[f72,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f986,plain,
    ( ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK2) ),
    inference(subsumption_resolution,[],[f985,f73])).

fof(f985,plain,
    ( ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f984,f74])).

fof(f984,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f581,f157])).

fof(f581,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_tops_2(sK0,X4,X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X4))))
      | r2_hidden(sK6(sK0,X4,X3,X5),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f578,f75])).

fof(f578,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X4))))
      | r2_hidden(sK6(sK0,X4,X3,X5),X3)
      | ~ r2_hidden(X5,k1_tops_2(sK0,X4,X3)) ) ),
    inference(duplicate_literal_removal,[],[f573])).

fof(f573,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X4))))
      | r2_hidden(sK6(sK0,X4,X3,X5),X3)
      | ~ r2_hidden(X5,k1_tops_2(sK0,X4,X3)) ) ),
    inference(resolution,[],[f125,f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',d3_tops_2)).

fof(f23845,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f23844,f74])).

fof(f23844,plain,(
    ! [X0] :
      ( r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f23843])).

fof(f23843,plain,(
    ! [X0] :
      ( r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f23823,f125])).

fof(f23823,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | r2_hidden(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0) ) ),
    inference(backward_demodulation,[],[f6097,f2873])).

fof(f2873,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(k3_xboole_0(sK1,sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)))),k1_tops_2(sK0,sK1,X0))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0) ) ),
    inference(forward_demodulation,[],[f2872,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',commutativity_k3_xboole_0)).

fof(f2872,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0) ) ),
    inference(forward_demodulation,[],[f2871,f131])).

fof(f131,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1) ),
    inference(resolution,[],[f74,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t40_tops_2.p',redefinition_k9_subset_1)).

fof(f2871,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2870,f116])).

fof(f2870,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2869,f75])).

fof(f2869,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2868,f74])).

fof(f2868,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2865,f825])).

fof(f2865,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),X0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(superposition,[],[f121,f1438])).

fof(f1438,plain,(
    k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f1437,f73])).

fof(f1437,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1436,f825])).

fof(f1436,plain,
    ( ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1435,f74])).

fof(f1435,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f582,f157])).

fof(f582,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_tops_2(sK0,X7,X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X7))))
      | k9_subset_1(u1_struct_0(sK0),sK6(sK0,X7,X6,X8),X7) = X8
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f577,f75])).

fof(f577,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X7))))
      | k9_subset_1(u1_struct_0(sK0),sK6(sK0,X7,X6,X8),X7) = X8
      | ~ r2_hidden(X8,k1_tops_2(sK0,X7,X6)) ) ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X7))))
      | k9_subset_1(u1_struct_0(sK0),sK6(sK0,X7,X6,X8),X7) = X8
      | ~ r2_hidden(X8,k1_tops_2(sK0,X7,X6)) ) ),
    inference(resolution,[],[f125,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X5,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X5,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | k9_subset_1(u1_struct_0(X0),X5,X1) != X4
      | r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6097,plain,(
    k3_xboole_0(sK1,sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)))) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(superposition,[],[f2863,f94])).

fof(f2863,plain,(
    k3_xboole_0(sK6(sK0,sK1,sK2,sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1) = sK9(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(superposition,[],[f1438,f131])).
%------------------------------------------------------------------------------
