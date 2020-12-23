%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t11_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 (1131 expanded)
%              Number of leaves         :    7 ( 359 expanded)
%              Depth                    :   26
%              Number of atoms          :  343 (10090 expanded)
%              Number of equality atoms :   27 ( 190 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f509,plain,(
    $false ),
    inference(subsumption_resolution,[],[f508,f226])).

fof(f226,plain,(
    r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(forward_demodulation,[],[f224,f134])).

fof(f134,plain,(
    k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1) ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_waybel_0(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) )
    & ( ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        & r1_waybel_0(sK0,sK1,sK2) )
      | r2_hidden(sK2,k2_yellow19(sK0,sK1)) )
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ r1_waybel_0(X0,X1,X2)
                  | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
                & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & r1_waybel_0(X0,X1,X2) )
                  | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ r1_waybel_0(sK0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(sK0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
                  & r1_waybel_0(sK0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(sK0,X1)) ) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ r1_waybel_0(X0,sK1,X2)
              | ~ r2_hidden(X2,k2_yellow19(X0,sK1)) )
            & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,sK1,X2) )
              | r2_hidden(X2,k2_yellow19(X0,sK1)) ) )
        & l1_waybel_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ r1_waybel_0(X0,X1,X2)
            | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
          & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & r1_waybel_0(X0,X1,X2) )
            | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
     => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ r1_waybel_0(X0,X1,sK2)
          | ~ r2_hidden(sK2,k2_yellow19(X0,X1)) )
        & ( ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
            & r1_waybel_0(X0,X1,sK2) )
          | r2_hidden(sK2,k2_yellow19(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r2_hidden(X2,k2_yellow19(X0,X1))
              <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',t11_yellow19)).

fof(f133,plain,
    ( k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f132,plain,
    ( k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f126,plain,
    ( k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f73,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',d3_yellow19)).

fof(f73,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f224,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f223,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f223,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f222,f70])).

fof(f222,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f71])).

fof(f221,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f72])).

fof(f220,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f219,f73])).

fof(f219,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f74,f93])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_yellow19(X1,X2))
      | ~ r1_waybel_0(X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ r1_waybel_0(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r1_waybel_0(X1,X2,sK4(X0,X1,X2))
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_0(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_waybel_0(X1,X2,sK4(X0,X1,X2))
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( r1_waybel_0(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( r1_waybel_0(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',fraenkel_a_2_1_yellow19)).

fof(f74,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f508,plain,(
    ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f505,f497])).

fof(f497,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f496,f226])).

fof(f496,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f495,f134])).

fof(f495,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f494,f70])).

fof(f494,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f493,f71])).

fof(f493,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f492,f72])).

fof(f492,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f485,f73])).

fof(f485,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f80,f483])).

fof(f483,plain,(
    sK2 = sK4(sK2,sK0,sK1) ),
    inference(resolution,[],[f143,f226])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | sK4(X1,sK0,sK1) = X1 ) ),
    inference(forward_demodulation,[],[f142,f134])).

fof(f142,plain,(
    ! [X1] :
      ( sK4(X1,sK0,sK1) = X1
      | ~ r2_hidden(X1,a_2_1_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f70])).

fof(f141,plain,(
    ! [X1] :
      ( sK4(X1,sK0,sK1) = X1
      | ~ r2_hidden(X1,a_2_1_yellow19(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f71])).

fof(f140,plain,(
    ! [X1] :
      ( sK4(X1,sK0,sK1) = X1
      | ~ r2_hidden(X1,a_2_1_yellow19(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f72])).

fof(f129,plain,(
    ! [X1] :
      ( sK4(X1,sK0,sK1) = X1
      | ~ r2_hidden(X1,a_2_1_yellow19(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X1,X2,sK4(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f505,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(resolution,[],[f491,f76])).

fof(f76,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f491,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f490,f226])).

fof(f490,plain,
    ( ~ r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f489,f134])).

fof(f489,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f488,f70])).

fof(f488,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f487,f71])).

fof(f487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f486,f72])).

fof(f486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f484,f73])).

fof(f484,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f78,f483])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
