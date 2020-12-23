%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:13 EST 2020

% Result     : Theorem 23.77s
% Output     : CNFRefutation 23.77s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_24823)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
     => ( ( ~ m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))))
          | ~ v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5))
          | ~ v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))
          | ~ v1_funct_1(k9_tmap_1(X0,sK5))
          | ~ m1_pre_topc(sK5,X0)
          | ~ v1_tsep_1(sK5,X0) )
        & ( ( m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))))
            & v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5))
            & v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))
            & v1_funct_1(k9_tmap_1(X0,sK5)) )
          | ( m1_pre_topc(sK5,X0)
            & v1_tsep_1(sK5,X0) ) )
        & m1_pre_topc(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k9_tmap_1(X0,X1))
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) )
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1))
            | ~ v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))
            | ~ v1_funct_1(k9_tmap_1(sK4,X1))
            | ~ m1_pre_topc(X1,sK4)
            | ~ v1_tsep_1(X1,sK4) )
          & ( ( m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))))
              & v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1))
              & v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))
              & v1_funct_1(k9_tmap_1(sK4,X1)) )
            | ( m1_pre_topc(X1,sK4)
              & v1_tsep_1(X1,sK4) ) )
          & m1_pre_topc(X1,sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
      | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
      | ~ m1_pre_topc(sK5,sK4)
      | ~ v1_tsep_1(sK5,sK4) )
    & ( ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
        & v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
        & v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
        & v1_funct_1(k9_tmap_1(sK4,sK5)) )
      | ( m1_pre_topc(sK5,sK4)
        & v1_tsep_1(sK5,sK4) ) )
    & m1_pre_topc(sK5,sK4)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f69,f71,f70])).

fof(f117,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f115,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f116,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f105,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f113,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f59,f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f63,f64])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f126,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f122,plain,
    ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_50,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5543,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_6395,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5543])).

cnf(c_8,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_39,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_390,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_39,c_25,c_24,c_23])).

cnf(c_391,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_5537,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ v2_pre_topc(X1_59)
    | v2_struct_0(X1_59)
    | ~ l1_pre_topc(X1_59)
    | k6_tmap_1(X1_59,u1_struct_0(X0_59)) = k8_tmap_1(X1_59,X0_59) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_6401,plain,
    ( k6_tmap_1(X0_59,u1_struct_0(X1_59)) = k8_tmap_1(X0_59,X1_59)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5537])).

cnf(c_8255,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5)
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_6401])).

cnf(c_53,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_54,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_55,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_56,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_8266,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8255,c_54,c_55,c_56])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5557,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | m1_subset_1(k7_tmap_1(X0_59,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58)))))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_6381,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_59,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58))))) = iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5557])).

cnf(c_3,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5571,plain,
    ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58)
    | ~ v1_funct_2(X5_58,X2_58,X3_58)
    | ~ v1_funct_2(X4_58,X0_58,X1_58)
    | ~ m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58)))
    | ~ m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X5_58)
    | ~ v1_funct_1(X4_58)
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6367,plain,
    ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58) = iProver_top
    | v1_funct_2(X5_58,X2_58,X3_58) != iProver_top
    | v1_funct_2(X4_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58))) != iProver_top
    | m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X5_58) != iProver_top
    | v1_funct_1(X4_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5571])).

cnf(c_8713,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X2_58)),X3_58,X3_58) = iProver_top
    | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
    | v1_funct_2(k7_tmap_1(X0_59,X2_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X2_58))) != iProver_top
    | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_funct_1(X3_58) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_59,X2_58)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_59,X2_58))) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6381,c_6367])).

cnf(c_24787,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_8713])).

cnf(c_5545,plain,
    ( m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(X1_59)))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_6393,plain,
    ( m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(X1_59))) = iProver_top
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5545])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5570,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | k7_tmap_1(X0_59,X0_58) = k6_partfun1(u1_struct_0(X0_59)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_6368,plain,
    ( k7_tmap_1(X0_59,X0_58) = k6_partfun1(u1_struct_0(X0_59))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5570])).

cnf(c_7941,plain,
    ( k7_tmap_1(X0_59,u1_struct_0(X1_59)) = k6_partfun1(u1_struct_0(X0_59))
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6368])).

cnf(c_10057,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4))
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_7941])).

cnf(c_10068,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10057,c_54,c_55,c_56])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5546,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | u1_struct_0(k6_tmap_1(X0_59,X0_58)) = u1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_6392,plain,
    ( u1_struct_0(k6_tmap_1(X0_59,X0_58)) = u1_struct_0(X0_59)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5546])).

cnf(c_8074,plain,
    ( u1_struct_0(k6_tmap_1(X0_59,u1_struct_0(X1_59))) = u1_struct_0(X0_59)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6392])).

cnf(c_10859,plain,
    ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_8074])).

cnf(c_10862,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10859,c_8266])).

cnf(c_11228,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10862,c_54,c_55,c_56])).

cnf(c_24818,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24787,c_8266,c_10068,c_11228])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_177,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_179,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_183,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_185,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_26,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_318,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42,c_50])).

cnf(c_2166,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_318])).

cnf(c_2167,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2166])).

cnf(c_2169,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_53,c_52,c_51])).

cnf(c_5533,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    inference(subtyping,[status(esa)],[c_2169])).

cnf(c_6405,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5533])).

cnf(c_7366,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_funct_1(k9_tmap_1(sK4,sK5)) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6405,c_6367])).

cnf(c_27,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2155,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_318])).

cnf(c_2156,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2155])).

cnf(c_2157,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2495,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_318])).

cnf(c_2496,plain,
    ( ~ v2_pre_topc(sK4)
    | v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2495])).

cnf(c_2497,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k9_tmap_1(sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_7606,plain,
    ( v1_funct_1(X2_58) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7366,c_54,c_55,c_56,c_2157,c_2497])).

cnf(c_7607,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7606])).

cnf(c_11232,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11228,c_7607])).

cnf(c_25289,plain,
    ( v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24818,c_54,c_55,c_56,c_57,c_69,c_72,c_117,c_120,c_179,c_185,c_8543,c_10081,c_11082,c_24823])).

cnf(c_25290,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
    | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X2_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_25289])).

cnf(c_5541,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_6397,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5541])).

cnf(c_40,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_5544,plain,
    ( m1_pre_topc(X0_59,X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_6394,plain,
    ( m1_pre_topc(X0_59,X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5544])).

cnf(c_8256,plain,
    ( k6_tmap_1(X0_59,u1_struct_0(X0_59)) = k8_tmap_1(X0_59,X0_59)
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_6401])).

cnf(c_8444,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_8256])).

cnf(c_68,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_5700,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5537])).

cnf(c_8536,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8444,c_53,c_52,c_51,c_68,c_5700])).

cnf(c_8711,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8536,c_6381])).

cnf(c_67,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_69,plain,
    ( m1_pre_topc(sK4,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_70,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_72,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_9009,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8711,c_54,c_55,c_56,c_69,c_72])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5565,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))))
    | ~ m1_pre_topc(X1_59,X0_59)
    | ~ v2_pre_topc(X0_59)
    | ~ v1_funct_1(X0_58)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | sK2(X0_59,X1_59,X0_58) = u1_struct_0(X1_59)
    | k9_tmap_1(X0_59,X1_59) = X0_58 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6373,plain,
    ( sK2(X0_59,X1_59,X0_58) = u1_struct_0(X1_59)
    | k9_tmap_1(X0_59,X1_59) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))))) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5565])).

cnf(c_9164,plain,
    ( sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9009,c_6373])).

cnf(c_71,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5555,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v1_funct_1(k7_tmap_1(X0_59,X0_58))
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_6468,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k7_tmap_1(sK4,X0_58))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5555])).

cnf(c_6638,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(X0_59)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6468])).

cnf(c_6640,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6638])).

cnf(c_21,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5556,plain,
    ( v1_funct_2(k7_tmap_1(X0_59,X0_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_6382,plain,
    ( v1_funct_2(k7_tmap_1(X0_59,X0_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58))) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5556])).

cnf(c_8639,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8536,c_6382])).

cnf(c_8641,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8639])).

cnf(c_9166,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)))
    | ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9164])).

cnf(c_41831,plain,
    ( sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9164,c_53,c_52,c_51,c_68,c_71,c_6640,c_8641,c_9166])).

cnf(c_10058,plain,
    ( k7_tmap_1(X0_59,u1_struct_0(X0_59)) = k6_partfun1(u1_struct_0(X0_59))
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_7941])).

cnf(c_10194,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4))
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_10058])).

cnf(c_6466,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k7_tmap_1(sK4,X0_58) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5570])).

cnf(c_6547,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k7_tmap_1(sK4,u1_struct_0(X0_59)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6466])).

cnf(c_6549,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6547])).

cnf(c_10205,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10194,c_53,c_52,c_51,c_68,c_71,c_6549])).

cnf(c_41833,plain,
    ( sK2(sK4,sK4,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(light_normalisation,[status(thm)],[c_41831,c_10205])).

cnf(c_9,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5566,plain,
    ( ~ r1_funct_2(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))),X0_58,k7_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58)))
    | ~ v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))))
    | ~ m1_pre_topc(X1_59,X0_59)
    | ~ v2_pre_topc(X0_59)
    | ~ v1_funct_1(X0_58)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | k9_tmap_1(X0_59,X1_59) = X0_58 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_6372,plain,
    ( k9_tmap_1(X0_59,X1_59) = X0_58
    | r1_funct_2(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))),X0_58,k7_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))))) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5566])).

cnf(c_41834,plain,
    ( k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4))
    | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK4))),k6_partfun1(u1_struct_0(sK4)),k7_tmap_1(sK4,u1_struct_0(sK4))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_41833,c_6372])).

cnf(c_10860,plain,
    ( u1_struct_0(k6_tmap_1(X0_59,u1_struct_0(X0_59))) = u1_struct_0(X0_59)
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_8074])).

cnf(c_10871,plain,
    ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_10860])).

cnf(c_10874,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK4)) = u1_struct_0(sK4)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10871,c_8536])).

cnf(c_11079,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK4)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10874,c_54,c_56])).

cnf(c_41836,plain,
    ( k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4))
    | r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41834,c_8536,c_10205,c_11079])).

cnf(c_57,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_6383,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_59,X0_58)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5555])).

cnf(c_7950,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v1_funct_1(k7_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6383])).

cnf(c_10081,plain,
    ( m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10068,c_7950])).

cnf(c_10207,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10205,c_9009])).

cnf(c_11081,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11079,c_10207])).

cnf(c_8910,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8639,c_54,c_55,c_56,c_69,c_72])).

cnf(c_10209,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10205,c_8910])).

cnf(c_11082,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11079,c_10209])).

cnf(c_8712,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_6381])).

cnf(c_2482,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_318])).

cnf(c_2483,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2482])).

cnf(c_2484,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_9018,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8712,c_54,c_55,c_56,c_2484])).

cnf(c_9165,plain,
    ( sK2(sK4,sK5,k7_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK5)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9018,c_6373])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(sK3(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2177,plain,
    ( ~ v3_pre_topc(sK3(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_318])).

cnf(c_2178,plain,
    ( ~ v3_pre_topc(sK3(sK4,sK5),sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2177])).

cnf(c_2179,plain,
    ( v3_pre_topc(sK3(sK4,sK5),sK4) != iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2178])).

cnf(c_5575,plain,
    ( X0_59 = X0_59 ),
    theory(equality)).

cnf(c_5625,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_5575])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK3(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5562,plain,
    ( v1_tsep_1(X0_59,X1_59)
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | sK3(X1_59,X0_59) = u1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_6376,plain,
    ( sK3(X0_59,X1_59) = u1_struct_0(X1_59)
    | v1_tsep_1(X1_59,X0_59) = iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5562])).

cnf(c_7062,plain,
    ( sK3(sK4,sK5) = u1_struct_0(sK5)
    | v1_tsep_1(sK5,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_6376])).

cnf(c_2498,plain,
    ( v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2496,c_53,c_52,c_51])).

cnf(c_2158,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2156,c_53,c_52,c_51])).

cnf(c_36,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_41,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_323,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41,c_50])).

cnf(c_324,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_742,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_324])).

cnf(c_743,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_747,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_53,c_52,c_51])).

cnf(c_748,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_747])).

cnf(c_2860,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2158,c_748])).

cnf(c_2866,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2169,c_2860])).

cnf(c_2939,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2498,c_2866])).

cnf(c_5531,plain,
    ( ~ v3_pre_topc(X0_58,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_2939])).

cnf(c_6407,plain,
    ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(X0_58,sK4) != iProver_top
    | v1_tsep_1(sK5,sK4) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5531])).

cnf(c_8268,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top
    | v1_tsep_1(sK5,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_6407])).

cnf(c_16,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_370,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_39])).

cnf(c_371,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_2468,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_318])).

cnf(c_2469,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2468])).

cnf(c_2470,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_7208,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0_59),sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,u1_struct_0(X0_59)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,u1_struct_0(X0_59)) != k9_tmap_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5531])).

cnf(c_7770,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7208])).

cnf(c_7771,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top
    | v1_tsep_1(sK5,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7770])).

cnf(c_8376,plain,
    ( v1_tsep_1(sK5,sK4) != iProver_top
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8268,c_54,c_55,c_56,c_2470,c_2484,c_7771,c_8255])).

cnf(c_8377,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v1_tsep_1(sK5,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_8376])).

cnf(c_34,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_346,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_21])).

cnf(c_45,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_778,plain,
    ( v3_pre_topc(X0,X1)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_346,c_45])).

cnf(c_779,plain,
    ( v3_pre_topc(X0,sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_783,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_tsep_1(sK5,sK4)
    | v3_pre_topc(X0,sK4)
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_779,c_53,c_52,c_51])).

cnf(c_784,plain,
    ( v3_pre_topc(X0,sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_783])).

cnf(c_5535,plain,
    ( v3_pre_topc(X0_58,sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58)))))
    | ~ v1_funct_1(k7_tmap_1(sK4,X0_58))
    | k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_784])).

cnf(c_6403,plain,
    ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(X0_58,sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,X0_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5535])).

cnf(c_5703,plain,
    ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(X0_58,sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,X0_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5535])).

cnf(c_6481,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,X0_58)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6468])).

cnf(c_6463,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58)))))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5557])).

cnf(c_6491,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6463])).

cnf(c_6904,plain,
    ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(X0_58,sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6403,c_54,c_55,c_56,c_5703,c_6481,c_6491])).

cnf(c_8269,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_6904])).

cnf(c_8439,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8269,c_56,c_2484,c_8377])).

cnf(c_8640,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_6382])).

cnf(c_5600,plain,
    ( ~ v3_pre_topc(X0_58,X0_59)
    | v3_pre_topc(X1_58,X1_59)
    | X1_59 != X0_59
    | X1_58 != X0_58 ),
    theory(equality)).

cnf(c_7213,plain,
    ( ~ v3_pre_topc(X0_58,X0_59)
    | v3_pre_topc(X1_58,sK4)
    | sK4 != X0_59
    | X1_58 != X0_58 ),
    inference(instantiation,[status(thm)],[c_5600])).

cnf(c_7799,plain,
    ( v3_pre_topc(X0_58,sK4)
    | ~ v3_pre_topc(u1_struct_0(X0_59),X1_59)
    | sK4 != X1_59
    | X0_58 != u1_struct_0(X0_59) ),
    inference(instantiation,[status(thm)],[c_7213])).

cnf(c_13396,plain,
    ( v3_pre_topc(sK3(sK4,sK5),sK4)
    | ~ v3_pre_topc(u1_struct_0(sK5),X0_59)
    | sK4 != X0_59
    | sK3(sK4,sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_7799])).

cnf(c_13403,plain,
    ( sK4 != X0_59
    | sK3(sK4,sK5) != u1_struct_0(sK5)
    | v3_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v3_pre_topc(u1_struct_0(sK5),X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13396])).

cnf(c_13405,plain,
    ( sK4 != sK4
    | sK3(sK4,sK5) != u1_struct_0(sK5)
    | v3_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13403])).

cnf(c_43459,plain,
    ( sK2(sK4,sK5,k7_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK5)
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9165,c_54,c_55,c_56,c_57,c_2179,c_2484,c_5625,c_7062,c_8377,c_8439,c_8640,c_13405])).

cnf(c_43463,plain,
    ( sK2(sK4,sK5,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK5)
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_43459,c_10068])).

cnf(c_43465,plain,
    ( sK2(sK4,sK5,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43463,c_53,c_52,c_51,c_56,c_50,c_57,c_2179,c_5625,c_6866,c_10075,c_10072,c_10073,c_10085,c_10376,c_13405])).

cnf(c_43467,plain,
    ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
    | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k6_partfun1(u1_struct_0(sK4)),k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_43465,c_6372])).

cnf(c_43469,plain,
    ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
    | r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_43467,c_8266,c_10068,c_11228])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5558,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | v1_pre_topc(k6_tmap_1(X0_59,X0_58))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_6380,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v1_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5558])).

cnf(c_7807,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | v1_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6380])).

cnf(c_11101,plain,
    ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
    | v1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11079,c_7807])).

cnf(c_19654,plain,
    ( v1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_11101])).

cnf(c_115,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(k8_tmap_1(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_117,plain,
    ( m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK4)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_118,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_120,plain,
    ( m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5548,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ v2_struct_0(k6_tmap_1(X0_59,X0_58))
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_6390,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(k6_tmap_1(X0_59,X0_58)) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5548])).

cnf(c_7269,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(k6_tmap_1(X1_59,u1_struct_0(X0_59))) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6390])).

cnf(c_8543,plain,
    ( m1_pre_topc(sK4,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(k8_tmap_1(sK4,sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8536,c_7269])).

cnf(c_24125,plain,
    ( v1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19654,c_54,c_55,c_56,c_69,c_117,c_120,c_8543])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK1(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5568,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ v1_pre_topc(X2_59)
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | k8_tmap_1(X1_59,X0_59) = X2_59
    | sK1(X1_59,X0_59,X2_59) = u1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6370,plain,
    ( k8_tmap_1(X0_59,X1_59) = X2_59
    | sK1(X0_59,X1_59,X2_59) = u1_struct_0(X1_59)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5568])).

cnf(c_8720,plain,
    ( k8_tmap_1(sK4,sK5) = X0_59
    | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_6370])).

cnf(c_8813,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_pre_topc(X0_59) != iProver_top
    | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
    | k8_tmap_1(sK4,sK5) = X0_59 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8720,c_54,c_55,c_56])).

cnf(c_8814,plain,
    ( k8_tmap_1(sK4,sK5) = X0_59
    | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_8813])).

cnf(c_24129,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = u1_struct_0(sK5)
    | v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24125,c_8814])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5559,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_pre_topc(k6_tmap_1(X0_59,X0_58))
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_6379,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5559])).

cnf(c_7718,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6379])).

cnf(c_11103,plain,
    ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11079,c_7718])).

cnf(c_19975,plain,
    ( v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_11103])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5560,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | l1_pre_topc(k6_tmap_1(X0_59,X0_58)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_6378,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5560])).

cnf(c_7676,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_6378])).

cnf(c_11105,plain,
    ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11079,c_7676])).

cnf(c_19978,plain,
    ( v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
    | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_11105])).

cnf(c_24253,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24129,c_54,c_55,c_56,c_69,c_117,c_120,c_8543,c_19975,c_19978])).

cnf(c_7,plain,
    ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5567,plain,
    ( m1_subset_1(sK1(X0_59,X1_59,X2_59),k1_zfmisc_1(u1_struct_0(X0_59)))
    | ~ m1_pre_topc(X1_59,X0_59)
    | ~ v1_pre_topc(X2_59)
    | ~ v2_pre_topc(X0_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X0_59)
    | ~ l1_pre_topc(X2_59)
    | k8_tmap_1(X0_59,X1_59) = X2_59 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6371,plain,
    ( k8_tmap_1(X0_59,X1_59) = X2_59
    | m1_subset_1(sK1(X0_59,X1_59,X2_59),k1_zfmisc_1(u1_struct_0(X0_59))) = iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5567])).

cnf(c_9133,plain,
    ( k8_tmap_1(X0_59,X1_59) = X2_59
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6371,c_6380])).

cnf(c_8721,plain,
    ( k8_tmap_1(X0_59,X0_59) = X1_59
    | sK1(X0_59,X0_59,X1_59) = u1_struct_0(X0_59)
    | v1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6394,c_6370])).

cnf(c_25520,plain,
    ( k8_tmap_1(sK4,sK4) = X0_59
    | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_8721])).

cnf(c_25841,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | k8_tmap_1(sK4,sK4) = X0_59
    | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25520,c_54,c_56])).

cnf(c_25842,plain,
    ( k8_tmap_1(sK4,sK4) = X0_59
    | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_25841])).

cnf(c_35240,plain,
    ( k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
    | k8_tmap_1(X0_59,X1_59) = X2_59
    | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9133,c_25842])).

cnf(c_9134,plain,
    ( k8_tmap_1(X0_59,X1_59) = X2_59
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_6371,c_6379])).

cnf(c_9135,plain,
    ( k8_tmap_1(X0_59,X1_59) = X2_59
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6371,c_6378])).

cnf(c_41580,plain,
    ( l1_pre_topc(X2_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
    | k8_tmap_1(X0_59,X1_59) = X2_59
    | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35240,c_9134,c_9135])).

cnf(c_41581,plain,
    ( k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
    | k8_tmap_1(X0_59,X1_59) = X2_59
    | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_41580])).

cnf(c_41586,plain,
    ( k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4)
    | k8_tmap_1(sK4,sK5) = X0_59
    | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_41581])).

cnf(c_41599,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v1_pre_topc(X0_59) != iProver_top
    | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
    | k8_tmap_1(sK4,sK5) = X0_59
    | k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41586,c_54,c_55,c_56])).

cnf(c_41600,plain,
    ( k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4)
    | k8_tmap_1(sK4,sK5) = X0_59
    | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
    | v1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_41599])).

cnf(c_41613,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))))) = u1_struct_0(sK4)
    | v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24125,c_41600])).

cnf(c_42394,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))))) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41613,c_54,c_55,c_56,c_69,c_117,c_120,c_8543,c_19975,c_19978])).

cnf(c_42396,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_24253,c_42394])).

cnf(c_42410,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(light_normalisation,[status(thm)],[c_42396,c_8266])).

cnf(c_42413,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | k8_tmap_1(sK4,sK4) != k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42410,c_6904])).

cnf(c_25849,plain,
    ( k6_tmap_1(X0_59,u1_struct_0(X1_59)) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k6_tmap_1(X0_59,u1_struct_0(X1_59))) = u1_struct_0(sK4)
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_59,u1_struct_0(X1_59))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(X1_59))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7807,c_25842])).

cnf(c_26351,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_25849])).

cnf(c_26437,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK4)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26351,c_8266])).

cnf(c_26438,plain,
    ( k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26437,c_8266])).

cnf(c_2519,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_318])).

cnf(c_2520,plain,
    ( v2_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2519])).

cnf(c_2530,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_318])).

cnf(c_2531,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2530])).

cnf(c_26456,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26438])).

cnf(c_28189,plain,
    ( k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26438,c_53,c_52,c_51,c_50,c_2520,c_2531,c_26456])).

cnf(c_44351,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42413,c_28189])).

cnf(c_44356,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24253,c_44351])).

cnf(c_44357,plain,
    ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
    | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
    | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44356,c_10068])).

cnf(c_6865,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | sK3(sK4,sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5562])).

cnf(c_6866,plain,
    ( sK3(sK4,sK5) = u1_struct_0(sK5)
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6865])).

cnf(c_10072,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
    | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10068,c_8439])).

cnf(c_10073,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
    | v1_tsep_1(sK5,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10068,c_8377])).

cnf(c_44440,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44357,c_56,c_57,c_2179,c_5625,c_6866,c_10072,c_10073,c_13405])).

cnf(c_44764,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41836,c_54,c_55,c_56,c_57,c_2179,c_5625,c_6866,c_10072,c_10073,c_10081,c_11081,c_11082,c_13405,c_43469])).

cnf(c_44768,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25290,c_44764])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44768,c_11082,c_11081,c_10081,c_185,c_179,c_57,c_56,c_55,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.77/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.77/3.50  
% 23.77/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.77/3.50  
% 23.77/3.50  ------  iProver source info
% 23.77/3.50  
% 23.77/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.77/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.77/3.50  git: non_committed_changes: false
% 23.77/3.50  git: last_make_outside_of_git: false
% 23.77/3.50  
% 23.77/3.50  ------ 
% 23.77/3.50  
% 23.77/3.50  ------ Input Options
% 23.77/3.50  
% 23.77/3.50  --out_options                           all
% 23.77/3.50  --tptp_safe_out                         true
% 23.77/3.50  --problem_path                          ""
% 23.77/3.50  --include_path                          ""
% 23.77/3.50  --clausifier                            res/vclausify_rel
% 23.77/3.50  --clausifier_options                    ""
% 23.77/3.50  --stdin                                 false
% 23.77/3.50  --stats_out                             all
% 23.77/3.50  
% 23.77/3.50  ------ General Options
% 23.77/3.50  
% 23.77/3.50  --fof                                   false
% 23.77/3.50  --time_out_real                         305.
% 23.77/3.50  --time_out_virtual                      -1.
% 23.77/3.50  --symbol_type_check                     false
% 23.77/3.50  --clausify_out                          false
% 23.77/3.50  --sig_cnt_out                           false
% 23.77/3.50  --trig_cnt_out                          false
% 23.77/3.50  --trig_cnt_out_tolerance                1.
% 23.77/3.50  --trig_cnt_out_sk_spl                   false
% 23.77/3.50  --abstr_cl_out                          false
% 23.77/3.50  
% 23.77/3.50  ------ Global Options
% 23.77/3.50  
% 23.77/3.50  --schedule                              default
% 23.77/3.50  --add_important_lit                     false
% 23.77/3.50  --prop_solver_per_cl                    1000
% 23.77/3.50  --min_unsat_core                        false
% 23.77/3.50  --soft_assumptions                      false
% 23.77/3.50  --soft_lemma_size                       3
% 23.77/3.50  --prop_impl_unit_size                   0
% 23.77/3.50  --prop_impl_unit                        []
% 23.77/3.50  --share_sel_clauses                     true
% 23.77/3.50  --reset_solvers                         false
% 23.77/3.50  --bc_imp_inh                            [conj_cone]
% 23.77/3.50  --conj_cone_tolerance                   3.
% 23.77/3.50  --extra_neg_conj                        none
% 23.77/3.50  --large_theory_mode                     true
% 23.77/3.50  --prolific_symb_bound                   200
% 23.77/3.50  --lt_threshold                          2000
% 23.77/3.50  --clause_weak_htbl                      true
% 23.77/3.50  --gc_record_bc_elim                     false
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing Options
% 23.77/3.50  
% 23.77/3.50  --preprocessing_flag                    true
% 23.77/3.50  --time_out_prep_mult                    0.1
% 23.77/3.50  --splitting_mode                        input
% 23.77/3.50  --splitting_grd                         true
% 23.77/3.50  --splitting_cvd                         false
% 23.77/3.50  --splitting_cvd_svl                     false
% 23.77/3.50  --splitting_nvd                         32
% 23.77/3.50  --sub_typing                            true
% 23.77/3.50  --prep_gs_sim                           true
% 23.77/3.50  --prep_unflatten                        true
% 23.77/3.50  --prep_res_sim                          true
% 23.77/3.50  --prep_upred                            true
% 23.77/3.50  --prep_sem_filter                       exhaustive
% 23.77/3.50  --prep_sem_filter_out                   false
% 23.77/3.50  --pred_elim                             true
% 23.77/3.50  --res_sim_input                         true
% 23.77/3.50  --eq_ax_congr_red                       true
% 23.77/3.50  --pure_diseq_elim                       true
% 23.77/3.50  --brand_transform                       false
% 23.77/3.50  --non_eq_to_eq                          false
% 23.77/3.50  --prep_def_merge                        true
% 23.77/3.50  --prep_def_merge_prop_impl              false
% 23.77/3.50  --prep_def_merge_mbd                    true
% 23.77/3.50  --prep_def_merge_tr_red                 false
% 23.77/3.50  --prep_def_merge_tr_cl                  false
% 23.77/3.50  --smt_preprocessing                     true
% 23.77/3.50  --smt_ac_axioms                         fast
% 23.77/3.50  --preprocessed_out                      false
% 23.77/3.50  --preprocessed_stats                    false
% 23.77/3.50  
% 23.77/3.50  ------ Abstraction refinement Options
% 23.77/3.50  
% 23.77/3.50  --abstr_ref                             []
% 23.77/3.50  --abstr_ref_prep                        false
% 23.77/3.50  --abstr_ref_until_sat                   false
% 23.77/3.50  --abstr_ref_sig_restrict                funpre
% 23.77/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.77/3.50  --abstr_ref_under                       []
% 23.77/3.50  
% 23.77/3.50  ------ SAT Options
% 23.77/3.50  
% 23.77/3.50  --sat_mode                              false
% 23.77/3.50  --sat_fm_restart_options                ""
% 23.77/3.50  --sat_gr_def                            false
% 23.77/3.50  --sat_epr_types                         true
% 23.77/3.50  --sat_non_cyclic_types                  false
% 23.77/3.50  --sat_finite_models                     false
% 23.77/3.50  --sat_fm_lemmas                         false
% 23.77/3.50  --sat_fm_prep                           false
% 23.77/3.50  --sat_fm_uc_incr                        true
% 23.77/3.50  --sat_out_model                         small
% 23.77/3.50  --sat_out_clauses                       false
% 23.77/3.50  
% 23.77/3.50  ------ QBF Options
% 23.77/3.50  
% 23.77/3.50  --qbf_mode                              false
% 23.77/3.50  --qbf_elim_univ                         false
% 23.77/3.50  --qbf_dom_inst                          none
% 23.77/3.50  --qbf_dom_pre_inst                      false
% 23.77/3.50  --qbf_sk_in                             false
% 23.77/3.50  --qbf_pred_elim                         true
% 23.77/3.50  --qbf_split                             512
% 23.77/3.50  
% 23.77/3.50  ------ BMC1 Options
% 23.77/3.50  
% 23.77/3.50  --bmc1_incremental                      false
% 23.77/3.50  --bmc1_axioms                           reachable_all
% 23.77/3.50  --bmc1_min_bound                        0
% 23.77/3.50  --bmc1_max_bound                        -1
% 23.77/3.50  --bmc1_max_bound_default                -1
% 23.77/3.50  --bmc1_symbol_reachability              true
% 23.77/3.50  --bmc1_property_lemmas                  false
% 23.77/3.50  --bmc1_k_induction                      false
% 23.77/3.50  --bmc1_non_equiv_states                 false
% 23.77/3.50  --bmc1_deadlock                         false
% 23.77/3.50  --bmc1_ucm                              false
% 23.77/3.50  --bmc1_add_unsat_core                   none
% 23.77/3.50  --bmc1_unsat_core_children              false
% 23.77/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.77/3.50  --bmc1_out_stat                         full
% 23.77/3.50  --bmc1_ground_init                      false
% 23.77/3.50  --bmc1_pre_inst_next_state              false
% 23.77/3.50  --bmc1_pre_inst_state                   false
% 23.77/3.50  --bmc1_pre_inst_reach_state             false
% 23.77/3.50  --bmc1_out_unsat_core                   false
% 23.77/3.50  --bmc1_aig_witness_out                  false
% 23.77/3.50  --bmc1_verbose                          false
% 23.77/3.50  --bmc1_dump_clauses_tptp                false
% 23.77/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.77/3.50  --bmc1_dump_file                        -
% 23.77/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.77/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.77/3.50  --bmc1_ucm_extend_mode                  1
% 23.77/3.50  --bmc1_ucm_init_mode                    2
% 23.77/3.50  --bmc1_ucm_cone_mode                    none
% 23.77/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.77/3.50  --bmc1_ucm_relax_model                  4
% 23.77/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.77/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.77/3.50  --bmc1_ucm_layered_model                none
% 23.77/3.50  --bmc1_ucm_max_lemma_size               10
% 23.77/3.50  
% 23.77/3.50  ------ AIG Options
% 23.77/3.50  
% 23.77/3.50  --aig_mode                              false
% 23.77/3.50  
% 23.77/3.50  ------ Instantiation Options
% 23.77/3.50  
% 23.77/3.50  --instantiation_flag                    true
% 23.77/3.50  --inst_sos_flag                         true
% 23.77/3.50  --inst_sos_phase                        true
% 23.77/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.77/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.77/3.50  --inst_lit_sel_side                     num_symb
% 23.77/3.50  --inst_solver_per_active                1400
% 23.77/3.50  --inst_solver_calls_frac                1.
% 23.77/3.50  --inst_passive_queue_type               priority_queues
% 23.77/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.77/3.50  --inst_passive_queues_freq              [25;2]
% 23.77/3.50  --inst_dismatching                      true
% 23.77/3.50  --inst_eager_unprocessed_to_passive     true
% 23.77/3.50  --inst_prop_sim_given                   true
% 23.77/3.50  --inst_prop_sim_new                     false
% 23.77/3.50  --inst_subs_new                         false
% 23.77/3.50  --inst_eq_res_simp                      false
% 23.77/3.50  --inst_subs_given                       false
% 23.77/3.50  --inst_orphan_elimination               true
% 23.77/3.50  --inst_learning_loop_flag               true
% 23.77/3.50  --inst_learning_start                   3000
% 23.77/3.50  --inst_learning_factor                  2
% 23.77/3.50  --inst_start_prop_sim_after_learn       3
% 23.77/3.50  --inst_sel_renew                        solver
% 23.77/3.50  --inst_lit_activity_flag                true
% 23.77/3.50  --inst_restr_to_given                   false
% 23.77/3.50  --inst_activity_threshold               500
% 23.77/3.50  --inst_out_proof                        true
% 23.77/3.50  
% 23.77/3.50  ------ Resolution Options
% 23.77/3.50  
% 23.77/3.50  --resolution_flag                       true
% 23.77/3.50  --res_lit_sel                           adaptive
% 23.77/3.50  --res_lit_sel_side                      none
% 23.77/3.50  --res_ordering                          kbo
% 23.77/3.50  --res_to_prop_solver                    active
% 23.77/3.50  --res_prop_simpl_new                    false
% 23.77/3.50  --res_prop_simpl_given                  true
% 23.77/3.50  --res_passive_queue_type                priority_queues
% 23.77/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.77/3.50  --res_passive_queues_freq               [15;5]
% 23.77/3.50  --res_forward_subs                      full
% 23.77/3.50  --res_backward_subs                     full
% 23.77/3.50  --res_forward_subs_resolution           true
% 23.77/3.50  --res_backward_subs_resolution          true
% 23.77/3.50  --res_orphan_elimination                true
% 23.77/3.50  --res_time_limit                        2.
% 23.77/3.50  --res_out_proof                         true
% 23.77/3.50  
% 23.77/3.50  ------ Superposition Options
% 23.77/3.50  
% 23.77/3.50  --superposition_flag                    true
% 23.77/3.50  --sup_passive_queue_type                priority_queues
% 23.77/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.77/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.77/3.50  --demod_completeness_check              fast
% 23.77/3.50  --demod_use_ground                      true
% 23.77/3.50  --sup_to_prop_solver                    passive
% 23.77/3.50  --sup_prop_simpl_new                    true
% 23.77/3.50  --sup_prop_simpl_given                  true
% 23.77/3.50  --sup_fun_splitting                     true
% 23.77/3.50  --sup_smt_interval                      50000
% 23.77/3.50  
% 23.77/3.50  ------ Superposition Simplification Setup
% 23.77/3.50  
% 23.77/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.77/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.77/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.77/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.77/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.77/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.77/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.77/3.50  --sup_immed_triv                        [TrivRules]
% 23.77/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.50  --sup_immed_bw_main                     []
% 23.77/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.77/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.77/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.50  --sup_input_bw                          []
% 23.77/3.50  
% 23.77/3.50  ------ Combination Options
% 23.77/3.50  
% 23.77/3.50  --comb_res_mult                         3
% 23.77/3.50  --comb_sup_mult                         2
% 23.77/3.50  --comb_inst_mult                        10
% 23.77/3.50  
% 23.77/3.50  ------ Debug Options
% 23.77/3.50  
% 23.77/3.50  --dbg_backtrace                         false
% 23.77/3.50  --dbg_dump_prop_clauses                 false
% 23.77/3.50  --dbg_dump_prop_clauses_file            -
% 23.77/3.50  --dbg_out_stat                          false
% 23.77/3.50  ------ Parsing...
% 23.77/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.77/3.50  ------ Proving...
% 23.77/3.50  ------ Problem Properties 
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  clauses                                 42
% 23.77/3.50  conjectures                             4
% 23.77/3.50  EPR                                     5
% 23.77/3.50  Horn                                    15
% 23.77/3.50  unary                                   7
% 23.77/3.50  binary                                  2
% 23.77/3.50  lits                                    200
% 23.77/3.50  lits eq                                 18
% 23.77/3.50  fd_pure                                 0
% 23.77/3.50  fd_pseudo                               0
% 23.77/3.50  fd_cond                                 0
% 23.77/3.50  fd_pseudo_cond                          6
% 23.77/3.50  AC symbols                              0
% 23.77/3.50  
% 23.77/3.50  ------ Schedule dynamic 5 is on 
% 23.77/3.50  
% 23.77/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  ------ 
% 23.77/3.50  Current options:
% 23.77/3.50  ------ 
% 23.77/3.50  
% 23.77/3.50  ------ Input Options
% 23.77/3.50  
% 23.77/3.50  --out_options                           all
% 23.77/3.50  --tptp_safe_out                         true
% 23.77/3.50  --problem_path                          ""
% 23.77/3.50  --include_path                          ""
% 23.77/3.50  --clausifier                            res/vclausify_rel
% 23.77/3.50  --clausifier_options                    ""
% 23.77/3.50  --stdin                                 false
% 23.77/3.50  --stats_out                             all
% 23.77/3.50  
% 23.77/3.50  ------ General Options
% 23.77/3.50  
% 23.77/3.50  --fof                                   false
% 23.77/3.50  --time_out_real                         305.
% 23.77/3.50  --time_out_virtual                      -1.
% 23.77/3.50  --symbol_type_check                     false
% 23.77/3.50  --clausify_out                          false
% 23.77/3.50  --sig_cnt_out                           false
% 23.77/3.50  --trig_cnt_out                          false
% 23.77/3.50  --trig_cnt_out_tolerance                1.
% 23.77/3.50  --trig_cnt_out_sk_spl                   false
% 23.77/3.50  --abstr_cl_out                          false
% 23.77/3.50  
% 23.77/3.50  ------ Global Options
% 23.77/3.50  
% 23.77/3.50  --schedule                              default
% 23.77/3.50  --add_important_lit                     false
% 23.77/3.50  --prop_solver_per_cl                    1000
% 23.77/3.50  --min_unsat_core                        false
% 23.77/3.50  --soft_assumptions                      false
% 23.77/3.50  --soft_lemma_size                       3
% 23.77/3.50  --prop_impl_unit_size                   0
% 23.77/3.50  --prop_impl_unit                        []
% 23.77/3.50  --share_sel_clauses                     true
% 23.77/3.50  --reset_solvers                         false
% 23.77/3.50  --bc_imp_inh                            [conj_cone]
% 23.77/3.50  --conj_cone_tolerance                   3.
% 23.77/3.50  --extra_neg_conj                        none
% 23.77/3.50  --large_theory_mode                     true
% 23.77/3.50  --prolific_symb_bound                   200
% 23.77/3.50  --lt_threshold                          2000
% 23.77/3.50  --clause_weak_htbl                      true
% 23.77/3.50  --gc_record_bc_elim                     false
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing Options
% 23.77/3.50  
% 23.77/3.50  --preprocessing_flag                    true
% 23.77/3.50  --time_out_prep_mult                    0.1
% 23.77/3.50  --splitting_mode                        input
% 23.77/3.50  --splitting_grd                         true
% 23.77/3.50  --splitting_cvd                         false
% 23.77/3.50  --splitting_cvd_svl                     false
% 23.77/3.50  --splitting_nvd                         32
% 23.77/3.50  --sub_typing                            true
% 23.77/3.50  --prep_gs_sim                           true
% 23.77/3.50  --prep_unflatten                        true
% 23.77/3.50  --prep_res_sim                          true
% 23.77/3.50  --prep_upred                            true
% 23.77/3.50  --prep_sem_filter                       exhaustive
% 23.77/3.50  --prep_sem_filter_out                   false
% 23.77/3.50  --pred_elim                             true
% 23.77/3.50  --res_sim_input                         true
% 23.77/3.50  --eq_ax_congr_red                       true
% 23.77/3.50  --pure_diseq_elim                       true
% 23.77/3.50  --brand_transform                       false
% 23.77/3.50  --non_eq_to_eq                          false
% 23.77/3.50  --prep_def_merge                        true
% 23.77/3.50  --prep_def_merge_prop_impl              false
% 23.77/3.50  --prep_def_merge_mbd                    true
% 23.77/3.50  --prep_def_merge_tr_red                 false
% 23.77/3.50  --prep_def_merge_tr_cl                  false
% 23.77/3.50  --smt_preprocessing                     true
% 23.77/3.50  --smt_ac_axioms                         fast
% 23.77/3.50  --preprocessed_out                      false
% 23.77/3.50  --preprocessed_stats                    false
% 23.77/3.50  
% 23.77/3.50  ------ Abstraction refinement Options
% 23.77/3.50  
% 23.77/3.50  --abstr_ref                             []
% 23.77/3.50  --abstr_ref_prep                        false
% 23.77/3.50  --abstr_ref_until_sat                   false
% 23.77/3.50  --abstr_ref_sig_restrict                funpre
% 23.77/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.77/3.50  --abstr_ref_under                       []
% 23.77/3.50  
% 23.77/3.50  ------ SAT Options
% 23.77/3.50  
% 23.77/3.50  --sat_mode                              false
% 23.77/3.50  --sat_fm_restart_options                ""
% 23.77/3.50  --sat_gr_def                            false
% 23.77/3.50  --sat_epr_types                         true
% 23.77/3.50  --sat_non_cyclic_types                  false
% 23.77/3.50  --sat_finite_models                     false
% 23.77/3.50  --sat_fm_lemmas                         false
% 23.77/3.50  --sat_fm_prep                           false
% 23.77/3.50  --sat_fm_uc_incr                        true
% 23.77/3.50  --sat_out_model                         small
% 23.77/3.50  --sat_out_clauses                       false
% 23.77/3.50  
% 23.77/3.50  ------ QBF Options
% 23.77/3.50  
% 23.77/3.50  --qbf_mode                              false
% 23.77/3.50  --qbf_elim_univ                         false
% 23.77/3.50  --qbf_dom_inst                          none
% 23.77/3.50  --qbf_dom_pre_inst                      false
% 23.77/3.50  --qbf_sk_in                             false
% 23.77/3.50  --qbf_pred_elim                         true
% 23.77/3.50  --qbf_split                             512
% 23.77/3.50  
% 23.77/3.50  ------ BMC1 Options
% 23.77/3.50  
% 23.77/3.50  --bmc1_incremental                      false
% 23.77/3.50  --bmc1_axioms                           reachable_all
% 23.77/3.50  --bmc1_min_bound                        0
% 23.77/3.50  --bmc1_max_bound                        -1
% 23.77/3.50  --bmc1_max_bound_default                -1
% 23.77/3.50  --bmc1_symbol_reachability              true
% 23.77/3.50  --bmc1_property_lemmas                  false
% 23.77/3.50  --bmc1_k_induction                      false
% 23.77/3.50  --bmc1_non_equiv_states                 false
% 23.77/3.50  --bmc1_deadlock                         false
% 23.77/3.50  --bmc1_ucm                              false
% 23.77/3.50  --bmc1_add_unsat_core                   none
% 23.77/3.50  --bmc1_unsat_core_children              false
% 23.77/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.77/3.50  --bmc1_out_stat                         full
% 23.77/3.50  --bmc1_ground_init                      false
% 23.77/3.50  --bmc1_pre_inst_next_state              false
% 23.77/3.50  --bmc1_pre_inst_state                   false
% 23.77/3.50  --bmc1_pre_inst_reach_state             false
% 23.77/3.50  --bmc1_out_unsat_core                   false
% 23.77/3.50  --bmc1_aig_witness_out                  false
% 23.77/3.50  --bmc1_verbose                          false
% 23.77/3.50  --bmc1_dump_clauses_tptp                false
% 23.77/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.77/3.50  --bmc1_dump_file                        -
% 23.77/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.77/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.77/3.50  --bmc1_ucm_extend_mode                  1
% 23.77/3.50  --bmc1_ucm_init_mode                    2
% 23.77/3.50  --bmc1_ucm_cone_mode                    none
% 23.77/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.77/3.50  --bmc1_ucm_relax_model                  4
% 23.77/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.77/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.77/3.50  --bmc1_ucm_layered_model                none
% 23.77/3.50  --bmc1_ucm_max_lemma_size               10
% 23.77/3.50  
% 23.77/3.50  ------ AIG Options
% 23.77/3.50  
% 23.77/3.50  --aig_mode                              false
% 23.77/3.50  
% 23.77/3.50  ------ Instantiation Options
% 23.77/3.50  
% 23.77/3.50  --instantiation_flag                    true
% 23.77/3.50  --inst_sos_flag                         true
% 23.77/3.50  --inst_sos_phase                        true
% 23.77/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.77/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.77/3.50  --inst_lit_sel_side                     none
% 23.77/3.50  --inst_solver_per_active                1400
% 23.77/3.50  --inst_solver_calls_frac                1.
% 23.77/3.50  --inst_passive_queue_type               priority_queues
% 23.77/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.77/3.50  --inst_passive_queues_freq              [25;2]
% 23.77/3.50  --inst_dismatching                      true
% 23.77/3.50  --inst_eager_unprocessed_to_passive     true
% 23.77/3.50  --inst_prop_sim_given                   true
% 23.77/3.50  --inst_prop_sim_new                     false
% 23.77/3.50  --inst_subs_new                         false
% 23.77/3.50  --inst_eq_res_simp                      false
% 23.77/3.50  --inst_subs_given                       false
% 23.77/3.50  --inst_orphan_elimination               true
% 23.77/3.50  --inst_learning_loop_flag               true
% 23.77/3.50  --inst_learning_start                   3000
% 23.77/3.50  --inst_learning_factor                  2
% 23.77/3.50  --inst_start_prop_sim_after_learn       3
% 23.77/3.50  --inst_sel_renew                        solver
% 23.77/3.50  --inst_lit_activity_flag                true
% 23.77/3.50  --inst_restr_to_given                   false
% 23.77/3.50  --inst_activity_threshold               500
% 23.77/3.50  --inst_out_proof                        true
% 23.77/3.50  
% 23.77/3.50  ------ Resolution Options
% 23.77/3.50  
% 23.77/3.50  --resolution_flag                       false
% 23.77/3.50  --res_lit_sel                           adaptive
% 23.77/3.50  --res_lit_sel_side                      none
% 23.77/3.50  --res_ordering                          kbo
% 23.77/3.50  --res_to_prop_solver                    active
% 23.77/3.50  --res_prop_simpl_new                    false
% 23.77/3.50  --res_prop_simpl_given                  true
% 23.77/3.51  --res_passive_queue_type                priority_queues
% 23.77/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.77/3.51  --res_passive_queues_freq               [15;5]
% 23.77/3.51  --res_forward_subs                      full
% 23.77/3.51  --res_backward_subs                     full
% 23.77/3.51  --res_forward_subs_resolution           true
% 23.77/3.51  --res_backward_subs_resolution          true
% 23.77/3.51  --res_orphan_elimination                true
% 23.77/3.51  --res_time_limit                        2.
% 23.77/3.51  --res_out_proof                         true
% 23.77/3.51  
% 23.77/3.51  ------ Superposition Options
% 23.77/3.51  
% 23.77/3.51  --superposition_flag                    true
% 23.77/3.51  --sup_passive_queue_type                priority_queues
% 23.77/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.77/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.77/3.51  --demod_completeness_check              fast
% 23.77/3.51  --demod_use_ground                      true
% 23.77/3.51  --sup_to_prop_solver                    passive
% 23.77/3.51  --sup_prop_simpl_new                    true
% 23.77/3.51  --sup_prop_simpl_given                  true
% 23.77/3.51  --sup_fun_splitting                     true
% 23.77/3.51  --sup_smt_interval                      50000
% 23.77/3.51  
% 23.77/3.51  ------ Superposition Simplification Setup
% 23.77/3.51  
% 23.77/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.77/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.77/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.77/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.77/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.77/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.77/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.77/3.51  --sup_immed_triv                        [TrivRules]
% 23.77/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.51  --sup_immed_bw_main                     []
% 23.77/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.77/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.77/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.77/3.51  --sup_input_bw                          []
% 23.77/3.51  
% 23.77/3.51  ------ Combination Options
% 23.77/3.51  
% 23.77/3.51  --comb_res_mult                         3
% 23.77/3.51  --comb_sup_mult                         2
% 23.77/3.51  --comb_inst_mult                        10
% 23.77/3.51  
% 23.77/3.51  ------ Debug Options
% 23.77/3.51  
% 23.77/3.51  --dbg_backtrace                         false
% 23.77/3.51  --dbg_dump_prop_clauses                 false
% 23.77/3.51  --dbg_dump_prop_clauses_file            -
% 23.77/3.51  --dbg_out_stat                          false
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  ------ Proving...
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  % SZS status Theorem for theBenchmark.p
% 23.77/3.51  
% 23.77/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.77/3.51  
% 23.77/3.51  fof(f18,conjecture,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f19,negated_conjecture,(
% 23.77/3.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 23.77/3.51    inference(negated_conjecture,[],[f18])).
% 23.77/3.51  
% 23.77/3.51  fof(f50,plain,(
% 23.77/3.51    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f19])).
% 23.77/3.51  
% 23.77/3.51  fof(f51,plain,(
% 23.77/3.51    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f50])).
% 23.77/3.51  
% 23.77/3.51  fof(f68,plain,(
% 23.77/3.51    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.77/3.51    inference(nnf_transformation,[],[f51])).
% 23.77/3.51  
% 23.77/3.51  fof(f69,plain,(
% 23.77/3.51    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f68])).
% 23.77/3.51  
% 23.77/3.51  fof(f71,plain,(
% 23.77/3.51    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))))) | ~v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5)) | ~v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))) | ~v1_funct_1(k9_tmap_1(X0,sK5)) | ~m1_pre_topc(sK5,X0) | ~v1_tsep_1(sK5,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))))) & v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5)) & v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))) & v1_funct_1(k9_tmap_1(X0,sK5))) | (m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0))) & m1_pre_topc(sK5,X0))) )),
% 23.77/3.51    introduced(choice_axiom,[])).
% 23.77/3.51  
% 23.77/3.51  fof(f70,plain,(
% 23.77/3.51    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))))) | ~v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1)) | ~v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))) | ~v1_funct_1(k9_tmap_1(sK4,X1)) | ~m1_pre_topc(X1,sK4) | ~v1_tsep_1(X1,sK4)) & ((m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))))) & v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1)) & v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))) & v1_funct_1(k9_tmap_1(sK4,X1))) | (m1_pre_topc(X1,sK4) & v1_tsep_1(X1,sK4))) & m1_pre_topc(X1,sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 23.77/3.51    introduced(choice_axiom,[])).
% 23.77/3.51  
% 23.77/3.51  fof(f72,plain,(
% 23.77/3.51    ((~m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k9_tmap_1(sK4,sK5)) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)) & ((m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) & v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) & v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) & v1_funct_1(k9_tmap_1(sK4,sK5))) | (m1_pre_topc(sK5,sK4) & v1_tsep_1(sK5,sK4))) & m1_pre_topc(sK5,sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 23.77/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f69,f71,f70])).
% 23.77/3.51  
% 23.77/3.51  fof(f117,plain,(
% 23.77/3.51    m1_pre_topc(sK5,sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f6,axiom,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f28,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f6])).
% 23.77/3.51  
% 23.77/3.51  fof(f29,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f28])).
% 23.77/3.51  
% 23.77/3.51  fof(f54,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(nnf_transformation,[],[f29])).
% 23.77/3.51  
% 23.77/3.51  fof(f55,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(rectify,[],[f54])).
% 23.77/3.51  
% 23.77/3.51  fof(f56,plain,(
% 23.77/3.51    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.77/3.51    introduced(choice_axiom,[])).
% 23.77/3.51  
% 23.77/3.51  fof(f57,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 23.77/3.51  
% 23.77/3.51  fof(f78,plain,(
% 23.77/3.51    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f57])).
% 23.77/3.51  
% 23.77/3.51  fof(f127,plain,(
% 23.77/3.51    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(equality_resolution,[],[f78])).
% 23.77/3.51  
% 23.77/3.51  fof(f128,plain,(
% 23.77/3.51    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(equality_resolution,[],[f127])).
% 23.77/3.51  
% 23.77/3.51  fof(f16,axiom,(
% 23.77/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f48,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(ennf_transformation,[],[f16])).
% 23.77/3.51  
% 23.77/3.51  fof(f112,plain,(
% 23.77/3.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f48])).
% 23.77/3.51  
% 23.77/3.51  fof(f11,axiom,(
% 23.77/3.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f38,plain,(
% 23.77/3.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f11])).
% 23.77/3.51  
% 23.77/3.51  fof(f39,plain,(
% 23.77/3.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f38])).
% 23.77/3.51  
% 23.77/3.51  fof(f96,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f39])).
% 23.77/3.51  
% 23.77/3.51  fof(f97,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f39])).
% 23.77/3.51  
% 23.77/3.51  fof(f98,plain,(
% 23.77/3.51    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f39])).
% 23.77/3.51  
% 23.77/3.51  fof(f114,plain,(
% 23.77/3.51    ~v2_struct_0(sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f115,plain,(
% 23.77/3.51    v2_pre_topc(sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f116,plain,(
% 23.77/3.51    l1_pre_topc(sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f10,axiom,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f36,plain,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f10])).
% 23.77/3.51  
% 23.77/3.51  fof(f37,plain,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f36])).
% 23.77/3.51  
% 23.77/3.51  fof(f95,plain,(
% 23.77/3.51    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f37])).
% 23.77/3.51  
% 23.77/3.51  fof(f4,axiom,(
% 23.77/3.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f24,plain,(
% 23.77/3.51    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 23.77/3.51    inference(ennf_transformation,[],[f4])).
% 23.77/3.51  
% 23.77/3.51  fof(f25,plain,(
% 23.77/3.51    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 23.77/3.51    inference(flattening,[],[f24])).
% 23.77/3.51  
% 23.77/3.51  fof(f76,plain,(
% 23.77/3.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f25])).
% 23.77/3.51  
% 23.77/3.51  fof(f5,axiom,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f26,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f5])).
% 23.77/3.51  
% 23.77/3.51  fof(f27,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f26])).
% 23.77/3.51  
% 23.77/3.51  fof(f77,plain,(
% 23.77/3.51    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f27])).
% 23.77/3.51  
% 23.77/3.51  fof(f14,axiom,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f44,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f14])).
% 23.77/3.51  
% 23.77/3.51  fof(f45,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f44])).
% 23.77/3.51  
% 23.77/3.51  fof(f105,plain,(
% 23.77/3.51    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f45])).
% 23.77/3.51  
% 23.77/3.51  fof(f3,axiom,(
% 23.77/3.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f22,plain,(
% 23.77/3.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f3])).
% 23.77/3.51  
% 23.77/3.51  fof(f23,plain,(
% 23.77/3.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f22])).
% 23.77/3.51  
% 23.77/3.51  fof(f75,plain,(
% 23.77/3.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f23])).
% 23.77/3.51  
% 23.77/3.51  fof(f1,axiom,(
% 23.77/3.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f20,plain,(
% 23.77/3.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(ennf_transformation,[],[f1])).
% 23.77/3.51  
% 23.77/3.51  fof(f73,plain,(
% 23.77/3.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f20])).
% 23.77/3.51  
% 23.77/3.51  fof(f12,axiom,(
% 23.77/3.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f40,plain,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f12])).
% 23.77/3.51  
% 23.77/3.51  fof(f41,plain,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f40])).
% 23.77/3.51  
% 23.77/3.51  fof(f101,plain,(
% 23.77/3.51    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f41])).
% 23.77/3.51  
% 23.77/3.51  fof(f125,plain,(
% 23.77/3.51    m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | m1_pre_topc(sK5,sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f100,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f41])).
% 23.77/3.51  
% 23.77/3.51  fof(f99,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f41])).
% 23.77/3.51  
% 23.77/3.51  fof(f17,axiom,(
% 23.77/3.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f49,plain,(
% 23.77/3.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(ennf_transformation,[],[f17])).
% 23.77/3.51  
% 23.77/3.51  fof(f113,plain,(
% 23.77/3.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f49])).
% 23.77/3.51  
% 23.77/3.51  fof(f7,axiom,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f30,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f7])).
% 23.77/3.51  
% 23.77/3.51  fof(f31,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f30])).
% 23.77/3.51  
% 23.77/3.51  fof(f58,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(nnf_transformation,[],[f31])).
% 23.77/3.51  
% 23.77/3.51  fof(f59,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(rectify,[],[f58])).
% 23.77/3.51  
% 23.77/3.51  fof(f60,plain,(
% 23.77/3.51    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.77/3.51    introduced(choice_axiom,[])).
% 23.77/3.51  
% 23.77/3.51  fof(f61,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f59,f60])).
% 23.77/3.51  
% 23.77/3.51  fof(f84,plain,(
% 23.77/3.51    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f61])).
% 23.77/3.51  
% 23.77/3.51  fof(f93,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f37])).
% 23.77/3.51  
% 23.77/3.51  fof(f94,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f37])).
% 23.77/3.51  
% 23.77/3.51  fof(f85,plain,(
% 23.77/3.51    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f61])).
% 23.77/3.51  
% 23.77/3.51  fof(f8,axiom,(
% 23.77/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f32,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(ennf_transformation,[],[f8])).
% 23.77/3.51  
% 23.77/3.51  fof(f33,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(flattening,[],[f32])).
% 23.77/3.51  
% 23.77/3.51  fof(f62,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(nnf_transformation,[],[f33])).
% 23.77/3.51  
% 23.77/3.51  fof(f63,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(rectify,[],[f62])).
% 23.77/3.51  
% 23.77/3.51  fof(f64,plain,(
% 23.77/3.51    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.77/3.51    introduced(choice_axiom,[])).
% 23.77/3.51  
% 23.77/3.51  fof(f65,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.77/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f63,f64])).
% 23.77/3.51  
% 23.77/3.51  fof(f89,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK3(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f65])).
% 23.77/3.51  
% 23.77/3.51  fof(f88,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f65])).
% 23.77/3.51  
% 23.77/3.51  fof(f15,axiom,(
% 23.77/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f46,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f15])).
% 23.77/3.51  
% 23.77/3.51  fof(f47,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f46])).
% 23.77/3.51  
% 23.77/3.51  fof(f66,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(nnf_transformation,[],[f47])).
% 23.77/3.51  
% 23.77/3.51  fof(f67,plain,(
% 23.77/3.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f66])).
% 23.77/3.51  
% 23.77/3.51  fof(f109,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f67])).
% 23.77/3.51  
% 23.77/3.51  fof(f126,plain,(
% 23.77/3.51    ~m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k9_tmap_1(sK4,sK5)) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f86,plain,(
% 23.77/3.51    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f65])).
% 23.77/3.51  
% 23.77/3.51  fof(f131,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.77/3.51    inference(equality_resolution,[],[f86])).
% 23.77/3.51  
% 23.77/3.51  fof(f111,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f67])).
% 23.77/3.51  
% 23.77/3.51  fof(f122,plain,(
% 23.77/3.51    v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | v1_tsep_1(sK5,sK4)),
% 23.77/3.51    inference(cnf_transformation,[],[f72])).
% 23.77/3.51  
% 23.77/3.51  fof(f13,axiom,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f42,plain,(
% 23.77/3.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f13])).
% 23.77/3.51  
% 23.77/3.51  fof(f43,plain,(
% 23.77/3.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f42])).
% 23.77/3.51  
% 23.77/3.51  fof(f103,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f43])).
% 23.77/3.51  
% 23.77/3.51  fof(f102,plain,(
% 23.77/3.51    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f43])).
% 23.77/3.51  
% 23.77/3.51  fof(f80,plain,(
% 23.77/3.51    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f57])).
% 23.77/3.51  
% 23.77/3.51  fof(f104,plain,(
% 23.77/3.51    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f43])).
% 23.77/3.51  
% 23.77/3.51  fof(f9,axiom,(
% 23.77/3.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 23.77/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.51  
% 23.77/3.51  fof(f34,plain,(
% 23.77/3.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.77/3.51    inference(ennf_transformation,[],[f9])).
% 23.77/3.51  
% 23.77/3.51  fof(f35,plain,(
% 23.77/3.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.77/3.51    inference(flattening,[],[f34])).
% 23.77/3.51  
% 23.77/3.51  fof(f92,plain,(
% 23.77/3.51    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f35])).
% 23.77/3.51  
% 23.77/3.51  fof(f79,plain,(
% 23.77/3.51    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.77/3.51    inference(cnf_transformation,[],[f57])).
% 23.77/3.51  
% 23.77/3.51  cnf(c_50,negated_conjecture,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f117]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5543,negated_conjecture,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_50]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6395,plain,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5543]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8,plain,
% 23.77/3.51      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 23.77/3.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f128]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_39,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f112]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | v1_pre_topc(k8_tmap_1(X1,X0))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f96]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f97]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_23,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 23.77/3.51      inference(cnf_transformation,[],[f98]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_390,plain,
% 23.77/3.51      ( ~ l1_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8,c_39,c_25,c_24,c_23]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_391,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_390]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5537,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0_59,X1_59)
% 23.77/3.51      | ~ v2_pre_topc(X1_59)
% 23.77/3.51      | v2_struct_0(X1_59)
% 23.77/3.51      | ~ l1_pre_topc(X1_59)
% 23.77/3.51      | k6_tmap_1(X1_59,u1_struct_0(X0_59)) = k8_tmap_1(X1_59,X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_391]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6401,plain,
% 23.77/3.51      ( k6_tmap_1(X0_59,u1_struct_0(X1_59)) = k8_tmap_1(X0_59,X1_59)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5537]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8255,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_6401]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_53,negated_conjecture,
% 23.77/3.51      ( ~ v2_struct_0(sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f114]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_54,plain,
% 23.77/3.51      ( v2_struct_0(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_52,negated_conjecture,
% 23.77/3.51      ( v2_pre_topc(sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f115]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_55,plain,
% 23.77/3.51      ( v2_pre_topc(sK4) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_51,negated_conjecture,
% 23.77/3.51      ( l1_pre_topc(sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f116]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_56,plain,
% 23.77/3.51      ( l1_pre_topc(sK4) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8266,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8255,c_54,c_55,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_20,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f95]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5557,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | m1_subset_1(k7_tmap_1(X0_59,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58)))))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_20]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6381,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | m1_subset_1(k7_tmap_1(X0_59,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58))))) = iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5557]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3,plain,
% 23.77/3.51      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 23.77/3.51      | ~ v1_funct_2(X5,X2,X3)
% 23.77/3.51      | ~ v1_funct_2(X4,X0,X1)
% 23.77/3.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 23.77/3.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.77/3.51      | ~ v1_funct_1(X5)
% 23.77/3.51      | ~ v1_funct_1(X4)
% 23.77/3.51      | v1_xboole_0(X1)
% 23.77/3.51      | v1_xboole_0(X3) ),
% 23.77/3.51      inference(cnf_transformation,[],[f76]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5571,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58)
% 23.77/3.51      | ~ v1_funct_2(X5_58,X2_58,X3_58)
% 23.77/3.51      | ~ v1_funct_2(X4_58,X0_58,X1_58)
% 23.77/3.51      | ~ m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58)))
% 23.77/3.51      | ~ m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 23.77/3.51      | ~ v1_funct_1(X5_58)
% 23.77/3.51      | ~ v1_funct_1(X4_58)
% 23.77/3.51      | v1_xboole_0(X1_58)
% 23.77/3.51      | v1_xboole_0(X3_58) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_3]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6367,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X5_58,X2_58,X3_58) != iProver_top
% 23.77/3.51      | v1_funct_2(X4_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58))) != iProver_top
% 23.77/3.51      | m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X5_58) != iProver_top
% 23.77/3.51      | v1_funct_1(X4_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(X3_58) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5571]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8713,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X2_58)),X3_58,X3_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | v1_funct_2(k7_tmap_1(X0_59,X2_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X2_58))) != iProver_top
% 23.77/3.51      | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_funct_1(X3_58) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(X0_59,X2_58)) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_59,X2_58))) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6381,c_6367]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24787,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_8713]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5545,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(X1_59)))
% 23.77/3.51      | ~ m1_pre_topc(X0_59,X1_59)
% 23.77/3.51      | ~ l1_pre_topc(X1_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_39]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6393,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(X1_59))) = iProver_top
% 23.77/3.51      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5545]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 23.77/3.51      inference(cnf_transformation,[],[f77]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5570,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | k7_tmap_1(X0_59,X0_58) = k6_partfun1(u1_struct_0(X0_59)) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_4]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6368,plain,
% 23.77/3.51      ( k7_tmap_1(X0_59,X0_58) = k6_partfun1(u1_struct_0(X0_59))
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5570]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7941,plain,
% 23.77/3.51      ( k7_tmap_1(X0_59,u1_struct_0(X1_59)) = k6_partfun1(u1_struct_0(X0_59))
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6368]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10057,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_7941]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10068,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_10057,c_54,c_55,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_33,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f105]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5546,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | u1_struct_0(k6_tmap_1(X0_59,X0_58)) = u1_struct_0(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_33]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6392,plain,
% 23.77/3.51      ( u1_struct_0(k6_tmap_1(X0_59,X0_58)) = u1_struct_0(X0_59)
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5546]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8074,plain,
% 23.77/3.51      ( u1_struct_0(k6_tmap_1(X0_59,u1_struct_0(X1_59))) = u1_struct_0(X0_59)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6392]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10859,plain,
% 23.77/3.51      ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_8074]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10862,plain,
% 23.77/3.51      ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_10859,c_8266]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11228,plain,
% 23.77/3.51      ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_10862,c_54,c_55,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24818,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_24787,c_8266,c_10068,c_11228]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2,plain,
% 23.77/3.51      ( v2_struct_0(X0)
% 23.77/3.51      | ~ v1_xboole_0(u1_struct_0(X0))
% 23.77/3.51      | ~ l1_struct_0(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f75]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_177,plain,
% 23.77/3.51      ( v2_struct_0(X0) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 23.77/3.51      | l1_struct_0(X0) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_179,plain,
% 23.77/3.51      ( v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 23.77/3.51      | l1_struct_0(sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_177]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_0,plain,
% 23.77/3.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f73]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_183,plain,
% 23.77/3.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_185,plain,
% 23.77/3.51      ( l1_pre_topc(sK4) != iProver_top
% 23.77/3.51      | l1_struct_0(sK4) = iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_183]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_26,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.77/3.51      | ~ m1_pre_topc(X1,X0)
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f101]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_42,negated_conjecture,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | m1_pre_topc(sK5,sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f125]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_318,negated_conjecture,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_42,c_50]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2166,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_26,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2167,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2166]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2169,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2167,c_53,c_52,c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5533,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_2169]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6405,plain,
% 23.77/3.51      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5533]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7366,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_funct_1(k9_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6405,c_6367]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_27,plain,
% 23.77/3.51      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.77/3.51      | ~ m1_pre_topc(X1,X0)
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f100]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2155,plain,
% 23.77/3.51      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_27,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2156,plain,
% 23.77/3.51      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2155]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2157,plain,
% 23.77/3.51      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_28,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v1_funct_1(k9_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f99]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2495,plain,
% 23.77/3.51      ( ~ v2_pre_topc(X0)
% 23.77/3.51      | v1_funct_1(k9_tmap_1(X0,X1))
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_28,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2496,plain,
% 23.77/3.51      ( ~ v2_pre_topc(sK4)
% 23.77/3.51      | v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2495]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2497,plain,
% 23.77/3.51      ( v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k9_tmap_1(sK4,sK5)) = iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7606,plain,
% 23.77/3.51      ( v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_7366,c_54,c_55,c_56,c_2157,c_2497]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7607,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_7606]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11232,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_11228,c_7607]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25289,plain,
% 23.77/3.51      ( v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_24818,c_54,c_55,c_56,c_57,c_69,c_72,c_117,c_120,c_179,
% 23.77/3.51                 c_185,c_8543,c_10081,c_11082,c_24823]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25290,plain,
% 23.77/3.51      ( r1_funct_2(X0_58,X1_58,u1_struct_0(sK4),u1_struct_0(sK4),X2_58,X2_58) = iProver_top
% 23.77/3.51      | v1_funct_2(X2_58,X0_58,X1_58) != iProver_top
% 23.77/3.51      | m1_subset_1(X2_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 23.77/3.51      | v1_funct_1(X2_58) != iProver_top
% 23.77/3.51      | v1_xboole_0(X1_58) = iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_25289]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5541,negated_conjecture,
% 23.77/3.51      ( v2_pre_topc(sK4) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_52]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6397,plain,
% 23.77/3.51      ( v2_pre_topc(sK4) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5541]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_40,plain,
% 23.77/3.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f113]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5544,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X0_59) | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_40]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6394,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5544]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8256,plain,
% 23.77/3.51      ( k6_tmap_1(X0_59,u1_struct_0(X0_59)) = k8_tmap_1(X0_59,X0_59)
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_6401]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8444,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6397,c_8256]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_68,plain,
% 23.77/3.51      ( m1_pre_topc(sK4,sK4) | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_40]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5700,plain,
% 23.77/3.51      ( ~ m1_pre_topc(sK4,sK4)
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5537]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8536,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK4)) = k8_tmap_1(sK4,sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8444,c_53,c_52,c_51,c_68,c_5700]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8711,plain,
% 23.77/3.51      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8536,c_6381]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_67,plain,
% 23.77/3.51      ( m1_pre_topc(X0,X0) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_69,plain,
% 23.77/3.51      ( m1_pre_topc(sK4,sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_67]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_70,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.77/3.51      | m1_pre_topc(X0,X1) != iProver_top
% 23.77/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_72,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_70]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9009,plain,
% 23.77/3.51      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8711,c_54,c_55,c_56,c_69,c_72]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10,plain,
% 23.77/3.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 23.77/3.51      | ~ m1_pre_topc(X2,X1)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | ~ v1_funct_1(X0)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | sK2(X1,X2,X0) = u1_struct_0(X2)
% 23.77/3.51      | k9_tmap_1(X1,X2) = X0 ),
% 23.77/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5565,plain,
% 23.77/3.51      ( ~ v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))
% 23.77/3.51      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))))
% 23.77/3.51      | ~ m1_pre_topc(X1_59,X0_59)
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | ~ v1_funct_1(X0_58)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | sK2(X0_59,X1_59,X0_58) = u1_struct_0(X1_59)
% 23.77/3.51      | k9_tmap_1(X0_59,X1_59) = X0_58 ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_10]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6373,plain,
% 23.77/3.51      ( sK2(X0_59,X1_59,X0_58) = u1_struct_0(X1_59)
% 23.77/3.51      | k9_tmap_1(X0_59,X1_59) = X0_58
% 23.77/3.51      | v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))) != iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))))) != iProver_top
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_funct_1(X0_58) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5565]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9164,plain,
% 23.77/3.51      ( sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4)
% 23.77/3.51      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_9009,c_6373]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_71,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_pre_topc(sK4,sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_39]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_22,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f93]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5555,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(X0_59,X0_58))
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_22]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6468,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,X0_58))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5555]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6638,plain,
% 23.77/3.51      ( ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(X0_59)))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_6468]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6640,plain,
% 23.77/3.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4)))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_6638]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_21,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 23.77/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f94]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5556,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(X0_59,X0_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58)))
% 23.77/3.51      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_21]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6382,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(X0_59,X0_58),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,X0_58))) = iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5556]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8639,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8536,c_6382]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8641,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)))
% 23.77/3.51      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_8639]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9166,plain,
% 23.77/3.51      ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)))
% 23.77/3.51      | ~ m1_pre_topc(sK4,sK4)
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK4)))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4) ),
% 23.77/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_9164]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41831,plain,
% 23.77/3.51      ( sK2(sK4,sK4,k7_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK4)) = k9_tmap_1(sK4,sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_9164,c_53,c_52,c_51,c_68,c_71,c_6640,c_8641,c_9166]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10058,plain,
% 23.77/3.51      ( k7_tmap_1(X0_59,u1_struct_0(X0_59)) = k6_partfun1(u1_struct_0(X0_59))
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_7941]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10194,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6397,c_10058]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6466,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5570]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6547,plain,
% 23.77/3.51      ( ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(X0_59)) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_6466]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6549,plain,
% 23.77/3.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_6547]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10205,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_10194,c_53,c_52,c_51,c_68,c_71,c_6549]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41833,plain,
% 23.77/3.51      ( sK2(sK4,sK4,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.77/3.51      | k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_41831,c_10205]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9,plain,
% 23.77/3.51      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
% 23.77/3.51      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.77/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.77/3.51      | ~ m1_pre_topc(X1,X0)
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | ~ v1_funct_1(X2)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | k9_tmap_1(X0,X1) = X2 ),
% 23.77/3.51      inference(cnf_transformation,[],[f85]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5566,plain,
% 23.77/3.51      ( ~ r1_funct_2(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))),X0_58,k7_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58)))
% 23.77/3.51      | ~ v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))
% 23.77/3.51      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)))))
% 23.77/3.51      | ~ m1_pre_topc(X1_59,X0_59)
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | ~ v1_funct_1(X0_58)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | k9_tmap_1(X0_59,X1_59) = X0_58 ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_9]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6372,plain,
% 23.77/3.51      ( k9_tmap_1(X0_59,X1_59) = X0_58
% 23.77/3.51      | r1_funct_2(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59)),u1_struct_0(X0_59),u1_struct_0(k6_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))),X0_58,k7_tmap_1(X0_59,sK2(X0_59,X1_59,X0_58))) != iProver_top
% 23.77/3.51      | v1_funct_2(X0_58,u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))) != iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(k8_tmap_1(X0_59,X1_59))))) != iProver_top
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_funct_1(X0_58) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5566]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41834,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK4))),k6_partfun1(u1_struct_0(sK4)),k7_tmap_1(sK4,u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) != iProver_top
% 23.77/3.51      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_41833,c_6372]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10860,plain,
% 23.77/3.51      ( u1_struct_0(k6_tmap_1(X0_59,u1_struct_0(X0_59))) = u1_struct_0(X0_59)
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_8074]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10871,plain,
% 23.77/3.51      ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6397,c_10860]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10874,plain,
% 23.77/3.51      ( u1_struct_0(k8_tmap_1(sK4,sK4)) = u1_struct_0(sK4)
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_10871,c_8536]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11079,plain,
% 23.77/3.51      ( u1_struct_0(k8_tmap_1(sK4,sK4)) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_10874,c_54,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41836,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK4) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 23.77/3.51      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_41834,c_8536,c_10205,c_11079]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_57,plain,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6383,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(X0_59,X0_58)) = iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5555]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7950,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
% 23.77/3.51      | v2_struct_0(X1_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6383]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10081,plain,
% 23.77/3.51      ( m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_10068,c_7950]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10207,plain,
% 23.77/3.51      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))))) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_10205,c_9009]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11081,plain,
% 23.77/3.51      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_11079,c_10207]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8910,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8639,c_54,c_55,c_56,c_69,c_72]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10209,plain,
% 23.77/3.51      ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK4))) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_10205,c_8910]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11082,plain,
% 23.77/3.51      ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_11079,c_10209]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8712,plain,
% 23.77/3.51      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_6381]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2482,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | sK5 != X0
% 23.77/3.51      | sK4 != X1 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_39,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2483,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2482]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2484,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9018,plain,
% 23.77/3.51      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8712,c_54,c_55,c_56,c_2484]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9165,plain,
% 23.77/3.51      ( sK2(sK4,sK5,k7_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK5)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_9018,c_6373]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_13,plain,
% 23.77/3.51      ( ~ v3_pre_topc(sK3(X0,X1),X0)
% 23.77/3.51      | v1_tsep_1(X1,X0)
% 23.77/3.51      | ~ m1_pre_topc(X1,X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f89]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2177,plain,
% 23.77/3.51      ( ~ v3_pre_topc(sK3(X0,X1),X0)
% 23.77/3.51      | v1_tsep_1(X1,X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_13,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2178,plain,
% 23.77/3.51      ( ~ v3_pre_topc(sK3(sK4,sK5),sK4)
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2177]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2179,plain,
% 23.77/3.51      ( v3_pre_topc(sK3(sK4,sK5),sK4) != iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2178]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5575,plain,( X0_59 = X0_59 ),theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5625,plain,
% 23.77/3.51      ( sK4 = sK4 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5575]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_14,plain,
% 23.77/3.51      ( v1_tsep_1(X0,X1)
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | sK3(X1,X0) = u1_struct_0(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f88]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5562,plain,
% 23.77/3.51      ( v1_tsep_1(X0_59,X1_59)
% 23.77/3.51      | ~ m1_pre_topc(X0_59,X1_59)
% 23.77/3.51      | ~ l1_pre_topc(X1_59)
% 23.77/3.51      | sK3(X1_59,X0_59) = u1_struct_0(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_14]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6376,plain,
% 23.77/3.51      ( sK3(X0_59,X1_59) = u1_struct_0(X1_59)
% 23.77/3.51      | v1_tsep_1(X1_59,X0_59) = iProver_top
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5562]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7062,plain,
% 23.77/3.51      ( sK3(sK4,sK5) = u1_struct_0(sK5)
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_6376]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2498,plain,
% 23.77/3.51      ( v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2496,c_53,c_52,c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2158,plain,
% 23.77/3.51      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2156,c_53,c_52,c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_36,plain,
% 23.77/3.51      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 23.77/3.51      | ~ v3_pre_topc(X1,X0)
% 23.77/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f109]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41,negated_conjecture,
% 23.77/3.51      ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ m1_pre_topc(sK5,sK4)
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 23.77/3.51      inference(cnf_transformation,[],[f126]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_323,plain,
% 23.77/3.51      ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_41,c_50]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_324,negated_conjecture,
% 23.77/3.51      ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_323]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_742,plain,
% 23.77/3.51      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v3_pre_topc(X0,X1)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | sK4 != X1 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_36,c_324]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_743,plain,
% 23.77/3.51      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_742]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_747,plain,
% 23.77/3.51      ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_743,c_53,c_52,c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_748,plain,
% 23.77/3.51      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 23.77/3.51      | ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_747]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2860,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(backward_subsumption_resolution,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2158,c_748]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2866,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(backward_subsumption_resolution,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2169,c_2860]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2939,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(backward_subsumption_resolution,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_2498,c_2866]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5531,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0_58,sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_2939]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6407,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(X0_58,sK4) != iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5531]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8268,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_6407]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_16,plain,
% 23.77/3.51      ( v3_pre_topc(u1_struct_0(X0),X1)
% 23.77/3.51      | ~ v1_tsep_1(X0,X1)
% 23.77/3.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f131]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_370,plain,
% 23.77/3.51      ( ~ v1_tsep_1(X0,X1)
% 23.77/3.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_16,c_39]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_371,plain,
% 23.77/3.51      ( v3_pre_topc(u1_struct_0(X0),X1)
% 23.77/3.51      | ~ v1_tsep_1(X0,X1)
% 23.77/3.51      | ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_370]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2468,plain,
% 23.77/3.51      ( v3_pre_topc(u1_struct_0(X0),X1)
% 23.77/3.51      | ~ v1_tsep_1(X0,X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | sK5 != X0
% 23.77/3.51      | sK4 != X1 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_371,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2469,plain,
% 23.77/3.51      ( v3_pre_topc(u1_struct_0(sK5),sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2468]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2470,plain,
% 23.77/3.51      ( v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7208,plain,
% 23.77/3.51      ( ~ v3_pre_topc(u1_struct_0(X0_59),sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | k6_tmap_1(sK4,u1_struct_0(X0_59)) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(X0_59)) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5531]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7770,plain,
% 23.77/3.51      ( ~ v3_pre_topc(u1_struct_0(sK5),sK4)
% 23.77/3.51      | ~ v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_7208]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7771,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_7770]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8376,plain,
% 23.77/3.51      ( v1_tsep_1(sK5,sK4) != iProver_top
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8268,c_54,c_55,c_56,c_2470,c_2484,c_7771,c_8255]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8377,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_8376]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_34,plain,
% 23.77/3.51      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 23.77/3.51      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 23.77/3.51      | v3_pre_topc(X1,X0)
% 23.77/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f111]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_346,plain,
% 23.77/3.51      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 23.77/3.51      | v3_pre_topc(X1,X0)
% 23.77/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_34,c_21]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_45,negated_conjecture,
% 23.77/3.51      ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 23.77/3.51      | v1_tsep_1(sK5,sK4) ),
% 23.77/3.51      inference(cnf_transformation,[],[f122]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_778,plain,
% 23.77/3.51      ( v3_pre_topc(X0,X1)
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | sK4 != X1 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_346,c_45]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_779,plain,
% 23.77/3.51      ( v3_pre_topc(X0,sK4)
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_778]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_783,plain,
% 23.77/3.51      ( ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | v3_pre_topc(X0,sK4)
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_779,c_53,c_52,c_51]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_784,plain,
% 23.77/3.51      ( v3_pre_topc(X0,sK4)
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 23.77/3.51      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_783]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5535,plain,
% 23.77/3.51      ( v3_pre_topc(X0_58,sK4)
% 23.77/3.51      | v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | ~ m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58)))))
% 23.77/3.51      | ~ v1_funct_1(k7_tmap_1(sK4,X0_58))
% 23.77/3.51      | k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_784]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6403,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(X0_58,sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,X0_58)) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5535]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5703,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(X0_58,sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,X0_58)) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5535]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6481,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,X0_58)) = iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_6468]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6463,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.77/3.51      | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58)))))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5557]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6491,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | m1_subset_1(k7_tmap_1(sK4,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_58))))) = iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_6463]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6904,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,X0_58) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k7_tmap_1(sK4,X0_58) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(X0_58,sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_6403,c_54,c_55,c_56,c_5703,c_6481,c_6491]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8269,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_6904]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8439,plain,
% 23.77/3.51      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8269,c_56,c_2484,c_8377]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8640,plain,
% 23.77/3.51      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_6382]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5600,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0_58,X0_59)
% 23.77/3.51      | v3_pre_topc(X1_58,X1_59)
% 23.77/3.51      | X1_59 != X0_59
% 23.77/3.51      | X1_58 != X0_58 ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7213,plain,
% 23.77/3.51      ( ~ v3_pre_topc(X0_58,X0_59)
% 23.77/3.51      | v3_pre_topc(X1_58,sK4)
% 23.77/3.51      | sK4 != X0_59
% 23.77/3.51      | X1_58 != X0_58 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5600]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7799,plain,
% 23.77/3.51      ( v3_pre_topc(X0_58,sK4)
% 23.77/3.51      | ~ v3_pre_topc(u1_struct_0(X0_59),X1_59)
% 23.77/3.51      | sK4 != X1_59
% 23.77/3.51      | X0_58 != u1_struct_0(X0_59) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_7213]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_13396,plain,
% 23.77/3.51      ( v3_pre_topc(sK3(sK4,sK5),sK4)
% 23.77/3.51      | ~ v3_pre_topc(u1_struct_0(sK5),X0_59)
% 23.77/3.51      | sK4 != X0_59
% 23.77/3.51      | sK3(sK4,sK5) != u1_struct_0(sK5) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_7799]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_13403,plain,
% 23.77/3.51      ( sK4 != X0_59
% 23.77/3.51      | sK3(sK4,sK5) != u1_struct_0(sK5)
% 23.77/3.51      | v3_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_13396]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_13405,plain,
% 23.77/3.51      ( sK4 != sK4
% 23.77/3.51      | sK3(sK4,sK5) != u1_struct_0(sK5)
% 23.77/3.51      | v3_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_13403]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_43459,plain,
% 23.77/3.51      ( sK2(sK4,sK5,k7_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK5)
% 23.77/3.51      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_9165,c_54,c_55,c_56,c_57,c_2179,c_2484,c_5625,c_7062,
% 23.77/3.51                 c_8377,c_8439,c_8640,c_13405]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_43463,plain,
% 23.77/3.51      ( sK2(sK4,sK5,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK5)
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_43459,c_10068]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_43465,plain,
% 23.77/3.51      ( sK2(sK4,sK5,k6_partfun1(u1_struct_0(sK4))) = u1_struct_0(sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_43463,c_53,c_52,c_51,c_56,c_50,c_57,c_2179,c_5625,
% 23.77/3.51                 c_6866,c_10075,c_10072,c_10073,c_10085,c_10376,c_13405]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_43467,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k6_partfun1(u1_struct_0(sK4)),k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 23.77/3.51      | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 23.77/3.51      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_43465,c_6372]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_43469,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 23.77/3.51      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_43467,c_8266,c_10068,c_11228]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_30,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X1,X0))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f103]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5558,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X0_59,X0_58))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_30]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6380,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5558]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7807,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X1_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6380]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11101,plain,
% 23.77/3.51      ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_11079,c_7807]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_19654,plain,
% 23.77/3.51      ( v1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
% 23.77/3.51      | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_11101]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_115,plain,
% 23.77/3.51      ( m1_pre_topc(X0,X1) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1) != iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(X1,X0)) = iProver_top
% 23.77/3.51      | v2_struct_0(X1) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_117,plain,
% 23.77/3.51      ( m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK4)) = iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_115]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_118,plain,
% 23.77/3.51      ( m1_pre_topc(X0,X1) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1) != iProver_top
% 23.77/3.51      | v2_struct_0(X1) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1) != iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_120,plain,
% 23.77/3.51      ( m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK4)) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_118]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_31,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f102]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5548,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ v2_struct_0(k6_tmap_1(X0_59,X0_58))
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_31]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6390,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | v2_struct_0(k6_tmap_1(X0_59,X0_58)) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5548]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7269,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X1_59) = iProver_top
% 23.77/3.51      | v2_struct_0(k6_tmap_1(X1_59,u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6390]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8543,plain,
% 23.77/3.51      ( m1_pre_topc(sK4,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(k8_tmap_1(sK4,sK4)) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8536,c_7269]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24125,plain,
% 23.77/3.51      ( v1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_19654,c_54,c_55,c_56,c_69,c_117,c_120,c_8543]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.77/3.51      | ~ v1_pre_topc(X2)
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | ~ v2_pre_topc(X2)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | ~ l1_pre_topc(X2)
% 23.77/3.51      | sK1(X1,X0,X2) = u1_struct_0(X0)
% 23.77/3.51      | k8_tmap_1(X1,X0) = X2 ),
% 23.77/3.51      inference(cnf_transformation,[],[f80]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5568,plain,
% 23.77/3.51      ( ~ m1_pre_topc(X0_59,X1_59)
% 23.77/3.51      | ~ v1_pre_topc(X2_59)
% 23.77/3.51      | ~ v2_pre_topc(X1_59)
% 23.77/3.51      | ~ v2_pre_topc(X2_59)
% 23.77/3.51      | v2_struct_0(X1_59)
% 23.77/3.51      | ~ l1_pre_topc(X1_59)
% 23.77/3.51      | ~ l1_pre_topc(X2_59)
% 23.77/3.51      | k8_tmap_1(X1_59,X0_59) = X2_59
% 23.77/3.51      | sK1(X1_59,X0_59,X2_59) = u1_struct_0(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_6]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6370,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | sK1(X0_59,X1_59,X2_59) = u1_struct_0(X1_59)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5568]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8720,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK5) = X0_59
% 23.77/3.51      | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_6370]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8813,plain,
% 23.77/3.51      ( l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
% 23.77/3.51      | k8_tmap_1(sK4,sK5) = X0_59 ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_8720,c_54,c_55,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8814,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK5) = X0_59
% 23.77/3.51      | sK1(sK4,sK5,X0_59) = u1_struct_0(sK5)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_8813]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24129,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = u1_struct_0(sK5)
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_24125,c_8814]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_29,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X1,X0))
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f104]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5559,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,X0_58))
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_29]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6379,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5559]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7718,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top
% 23.77/3.51      | v2_struct_0(X1_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6379]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11103,plain,
% 23.77/3.51      ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_11079,c_7718]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_19975,plain,
% 23.77/3.51      ( v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
% 23.77/3.51      | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_11103]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_17,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ v2_pre_topc(X1)
% 23.77/3.51      | v2_struct_0(X1)
% 23.77/3.51      | ~ l1_pre_topc(X1)
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 23.77/3.51      inference(cnf_transformation,[],[f92]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5560,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,X0_58)) ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_17]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6378,plain,
% 23.77/3.51      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_59))) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,X0_58)) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5560]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7676,plain,
% 23.77/3.51      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X1_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X1_59,u1_struct_0(X0_59))) = iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6393,c_6378]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11105,plain,
% 23.77/3.51      ( m1_pre_topc(k8_tmap_1(sK4,sK4),X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(sK4))) = iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_11079,c_7676]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_19978,plain,
% 23.77/3.51      ( v2_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top
% 23.77/3.51      | v2_struct_0(k8_tmap_1(sK4,sK4)) = iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK4)) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_11105]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24253,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) = u1_struct_0(sK5) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_24129,c_54,c_55,c_56,c_69,c_117,c_120,c_8543,c_19975,
% 23.77/3.51                 c_19978]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7,plain,
% 23.77/3.51      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | ~ m1_pre_topc(X1,X0)
% 23.77/3.51      | ~ v1_pre_topc(X2)
% 23.77/3.51      | ~ v2_pre_topc(X0)
% 23.77/3.51      | ~ v2_pre_topc(X2)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | ~ l1_pre_topc(X2)
% 23.77/3.51      | k8_tmap_1(X0,X1) = X2 ),
% 23.77/3.51      inference(cnf_transformation,[],[f79]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_5567,plain,
% 23.77/3.51      ( m1_subset_1(sK1(X0_59,X1_59,X2_59),k1_zfmisc_1(u1_struct_0(X0_59)))
% 23.77/3.51      | ~ m1_pre_topc(X1_59,X0_59)
% 23.77/3.51      | ~ v1_pre_topc(X2_59)
% 23.77/3.51      | ~ v2_pre_topc(X0_59)
% 23.77/3.51      | ~ v2_pre_topc(X2_59)
% 23.77/3.51      | v2_struct_0(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X0_59)
% 23.77/3.51      | ~ l1_pre_topc(X2_59)
% 23.77/3.51      | k8_tmap_1(X0_59,X1_59) = X2_59 ),
% 23.77/3.51      inference(subtyping,[status(esa)],[c_7]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6371,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | m1_subset_1(sK1(X0_59,X1_59,X2_59),k1_zfmisc_1(u1_struct_0(X0_59))) = iProver_top
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_5567]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9133,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6371,c_6380]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8721,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X0_59) = X1_59
% 23.77/3.51      | sK1(X0_59,X0_59,X1_59) = u1_struct_0(X0_59)
% 23.77/3.51      | v1_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X1_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X1_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6394,c_6370]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25520,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK4) = X0_59
% 23.77/3.51      | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6397,c_8721]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25841,plain,
% 23.77/3.51      ( l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | k8_tmap_1(sK4,sK4) = X0_59
% 23.77/3.51      | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_25520,c_54,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25842,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK4) = X0_59
% 23.77/3.51      | sK1(sK4,sK4,X0_59) = u1_struct_0(sK4)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_25841]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_35240,plain,
% 23.77/3.51      ( k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_9133,c_25842]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9134,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6371,c_6379]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9135,plain,
% 23.77/3.51      ( k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6371,c_6378]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41580,plain,
% 23.77/3.51      ( l1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_35240,c_9134,c_9135]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41581,plain,
% 23.77/3.51      ( k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | k8_tmap_1(X0_59,X1_59) = X2_59
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(X0_59,sK1(X0_59,X1_59,X2_59))) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X2_59) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X2_59) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_41580]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41586,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | k8_tmap_1(sK4,sK5) = X0_59
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_6395,c_41581]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41599,plain,
% 23.77/3.51      ( l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
% 23.77/3.51      | k8_tmap_1(sK4,sK5) = X0_59
% 23.77/3.51      | k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_41586,c_54,c_55,c_56]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41600,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,sK1(sK4,sK5,X0_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | k8_tmap_1(sK4,sK5) = X0_59
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,X0_59))) = u1_struct_0(sK4)
% 23.77/3.51      | v1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_41599]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_41613,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))))) = u1_struct_0(sK4)
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_24125,c_41600]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_42394,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))))) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_41613,c_54,c_55,c_56,c_69,c_117,c_120,c_8543,c_19975,
% 23.77/3.51                 c_19978]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_42396,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_24253,c_42394]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_42410,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k6_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_42396,c_8266]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_42413,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | k8_tmap_1(sK4,sK4) != k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_42410,c_6904]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25849,plain,
% 23.77/3.51      ( k6_tmap_1(X0_59,u1_struct_0(X1_59)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(X0_59,u1_struct_0(X1_59))) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | v2_pre_topc(k6_tmap_1(X0_59,u1_struct_0(X1_59))) != iProver_top
% 23.77/3.51      | v2_struct_0(X0_59) = iProver_top
% 23.77/3.51      | l1_pre_topc(X0_59) != iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(X0_59,u1_struct_0(X1_59))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_7807,c_25842]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_26351,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_8266,c_25849]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_26437,plain,
% 23.77/3.51      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK4)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_26351,c_8266]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_26438,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | v2_pre_topc(sK4) != iProver_top
% 23.77/3.51      | v2_struct_0(sK4) = iProver_top
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK5)) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_26437,c_8266]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2519,plain,
% 23.77/3.51      ( ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_pre_topc(k8_tmap_1(X0,X1))
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_24,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2520,plain,
% 23.77/3.51      ( v2_pre_topc(k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2519]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2530,plain,
% 23.77/3.51      ( ~ v2_pre_topc(X0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ l1_pre_topc(X0)
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(X0,X1))
% 23.77/3.51      | sK5 != X1
% 23.77/3.51      | sK4 != X0 ),
% 23.77/3.51      inference(resolution_lifted,[status(thm)],[c_23,c_318]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2531,plain,
% 23.77/3.51      ( ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | l1_pre_topc(k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ l1_pre_topc(sK4) ),
% 23.77/3.51      inference(unflattening,[status(thm)],[c_2530]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_26456,plain,
% 23.77/3.51      ( ~ m1_pre_topc(sK5,sK4)
% 23.77/3.51      | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ v2_pre_topc(sK4)
% 23.77/3.51      | v2_struct_0(sK4)
% 23.77/3.51      | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_26438]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_28189,plain,
% 23.77/3.51      ( k8_tmap_1(sK4,sK4) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_26438,c_53,c_52,c_51,c_50,c_2520,c_2531,c_26456]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44351,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)))) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_42413,c_28189]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44356,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 23.77/3.51      | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_24253,c_44351]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44357,plain,
% 23.77/3.51      ( k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4)) = k8_tmap_1(sK4,sK5)
% 23.77/3.51      | sK1(sK4,sK4,k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 23.77/3.51      | k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | v3_pre_topc(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),sK4) = iProver_top
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_subset_1(sK1(sK4,sK5,k6_tmap_1(k8_tmap_1(sK4,sK4),u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(light_normalisation,[status(thm)],[c_44356,c_10068]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6865,plain,
% 23.77/3.51      ( v1_tsep_1(sK5,sK4)
% 23.77/3.51      | ~ m1_pre_topc(sK5,sK4)
% 23.77/3.51      | ~ l1_pre_topc(sK4)
% 23.77/3.51      | sK3(sK4,sK5) = u1_struct_0(sK5) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_5562]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6866,plain,
% 23.77/3.51      ( sK3(sK4,sK5) = u1_struct_0(sK5)
% 23.77/3.51      | v1_tsep_1(sK5,sK4) = iProver_top
% 23.77/3.51      | m1_pre_topc(sK5,sK4) != iProver_top
% 23.77/3.51      | l1_pre_topc(sK4) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_6865]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10072,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | v3_pre_topc(u1_struct_0(sK5),sK4) = iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_10068,c_8439]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10073,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
% 23.77/3.51      | v1_tsep_1(sK5,sK4) != iProver_top ),
% 23.77/3.51      inference(demodulation,[status(thm)],[c_10068,c_8377]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44440,plain,
% 23.77/3.51      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_44357,c_56,c_57,c_2179,c_5625,c_6866,c_10072,c_10073,
% 23.77/3.51                 c_13405]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44764,plain,
% 23.77/3.51      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),k6_partfun1(u1_struct_0(sK4))) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_41836,c_54,c_55,c_56,c_57,c_2179,c_5625,c_6866,
% 23.77/3.51                 c_10072,c_10073,c_10081,c_11081,c_11082,c_13405,c_43469]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_44768,plain,
% 23.77/3.51      ( v1_funct_2(k6_partfun1(u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 23.77/3.51      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 23.77/3.51      | v1_funct_1(k6_partfun1(u1_struct_0(sK4))) != iProver_top
% 23.77/3.51      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_25290,c_44764]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(contradiction,plain,
% 23.77/3.51      ( $false ),
% 23.77/3.51      inference(minisat,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_44768,c_11082,c_11081,c_10081,c_185,c_179,c_57,c_56,
% 23.77/3.51                 c_55,c_54]) ).
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.77/3.51  
% 23.77/3.51  ------                               Statistics
% 23.77/3.51  
% 23.77/3.51  ------ General
% 23.77/3.51  
% 23.77/3.51  abstr_ref_over_cycles:                  0
% 23.77/3.51  abstr_ref_under_cycles:                 0
% 23.77/3.51  gc_basic_clause_elim:                   0
% 23.77/3.51  forced_gc_time:                         0
% 23.77/3.51  parsing_time:                           0.012
% 23.77/3.51  unif_index_cands_time:                  0.
% 23.77/3.51  unif_index_add_time:                    0.
% 23.77/3.51  orderings_time:                         0.
% 23.77/3.51  out_proof_time:                         0.064
% 23.77/3.51  total_time:                             2.768
% 23.77/3.51  num_of_symbols:                         68
% 23.77/3.51  num_of_terms:                           41632
% 23.77/3.51  
% 23.77/3.51  ------ Preprocessing
% 23.77/3.51  
% 23.77/3.51  num_of_splits:                          0
% 23.77/3.51  num_of_split_atoms:                     0
% 23.77/3.51  num_of_reused_defs:                     0
% 23.77/3.51  num_eq_ax_congr_red:                    37
% 23.77/3.51  num_of_sem_filtered_clauses:            5
% 23.77/3.51  num_of_subtypes:                        4
% 23.77/3.51  monotx_restored_types:                  0
% 23.77/3.51  sat_num_of_epr_types:                   0
% 23.77/3.51  sat_num_of_non_cyclic_types:            0
% 23.77/3.51  sat_guarded_non_collapsed_types:        2
% 23.77/3.51  num_pure_diseq_elim:                    0
% 23.77/3.51  simp_replaced_by:                       0
% 23.77/3.51  res_preprocessed:                       224
% 23.77/3.51  prep_upred:                             0
% 23.77/3.51  prep_unflattend:                        305
% 23.77/3.51  smt_new_axioms:                         0
% 23.77/3.51  pred_elim_cands:                        12
% 23.77/3.51  pred_elim:                              2
% 23.77/3.51  pred_elim_cl:                           3
% 23.77/3.51  pred_elim_cycles:                       14
% 23.77/3.51  merged_defs:                            0
% 23.77/3.51  merged_defs_ncl:                        0
% 23.77/3.51  bin_hyper_res:                          0
% 23.77/3.51  prep_cycles:                            4
% 23.77/3.51  pred_elim_time:                         0.106
% 23.77/3.51  splitting_time:                         0.
% 23.77/3.51  sem_filter_time:                        0.
% 23.77/3.51  monotx_time:                            0.
% 23.77/3.51  subtype_inf_time:                       0.001
% 23.77/3.51  
% 23.77/3.51  ------ Problem properties
% 23.77/3.51  
% 23.77/3.51  clauses:                                42
% 23.77/3.51  conjectures:                            4
% 23.77/3.51  epr:                                    5
% 23.77/3.51  horn:                                   15
% 23.77/3.51  ground:                                 7
% 23.77/3.51  unary:                                  7
% 23.77/3.51  binary:                                 2
% 23.77/3.51  lits:                                   200
% 23.77/3.51  lits_eq:                                18
% 23.77/3.51  fd_pure:                                0
% 23.77/3.51  fd_pseudo:                              0
% 23.77/3.51  fd_cond:                                0
% 23.77/3.51  fd_pseudo_cond:                         6
% 23.77/3.51  ac_symbols:                             0
% 23.77/3.51  
% 23.77/3.51  ------ Propositional Solver
% 23.77/3.51  
% 23.77/3.51  prop_solver_calls:                      32
% 23.77/3.51  prop_fast_solver_calls:                 5846
% 23.77/3.51  smt_solver_calls:                       0
% 23.77/3.51  smt_fast_solver_calls:                  0
% 23.77/3.51  prop_num_of_clauses:                    14119
% 23.77/3.51  prop_preprocess_simplified:             31413
% 23.77/3.51  prop_fo_subsumed:                       814
% 23.77/3.51  prop_solver_time:                       0.
% 23.77/3.51  smt_solver_time:                        0.
% 23.77/3.51  smt_fast_solver_time:                   0.
% 23.77/3.51  prop_fast_solver_time:                  0.
% 23.77/3.51  prop_unsat_core_time:                   0.002
% 23.77/3.51  
% 23.77/3.51  ------ QBF
% 23.77/3.51  
% 23.77/3.51  qbf_q_res:                              0
% 23.77/3.51  qbf_num_tautologies:                    0
% 23.77/3.51  qbf_prep_cycles:                        0
% 23.77/3.51  
% 23.77/3.51  ------ BMC1
% 23.77/3.51  
% 23.77/3.51  bmc1_current_bound:                     -1
% 23.77/3.51  bmc1_last_solved_bound:                 -1
% 23.77/3.51  bmc1_unsat_core_size:                   -1
% 23.77/3.51  bmc1_unsat_core_parents_size:           -1
% 23.77/3.51  bmc1_merge_next_fun:                    0
% 23.77/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.77/3.51  
% 23.77/3.51  ------ Instantiation
% 23.77/3.51  
% 23.77/3.51  inst_num_of_clauses:                    3617
% 23.77/3.51  inst_num_in_passive:                    514
% 23.77/3.51  inst_num_in_active:                     1817
% 23.77/3.51  inst_num_in_unprocessed:                1286
% 23.77/3.51  inst_num_of_loops:                      2010
% 23.77/3.51  inst_num_of_learning_restarts:          0
% 23.77/3.51  inst_num_moves_active_passive:          190
% 23.77/3.51  inst_lit_activity:                      0
% 23.77/3.51  inst_lit_activity_moves:                0
% 23.77/3.51  inst_num_tautologies:                   0
% 23.77/3.51  inst_num_prop_implied:                  0
% 23.77/3.51  inst_num_existing_simplified:           0
% 23.77/3.51  inst_num_eq_res_simplified:             0
% 23.77/3.51  inst_num_child_elim:                    0
% 23.77/3.51  inst_num_of_dismatching_blockings:      6629
% 23.77/3.51  inst_num_of_non_proper_insts:           6985
% 23.77/3.51  inst_num_of_duplicates:                 0
% 23.77/3.51  inst_inst_num_from_inst_to_res:         0
% 23.77/3.51  inst_dismatching_checking_time:         0.
% 23.77/3.51  
% 23.77/3.51  ------ Resolution
% 23.77/3.51  
% 23.77/3.51  res_num_of_clauses:                     0
% 23.77/3.51  res_num_in_passive:                     0
% 23.77/3.51  res_num_in_active:                      0
% 23.77/3.51  res_num_of_loops:                       228
% 23.77/3.51  res_forward_subset_subsumed:            311
% 23.77/3.51  res_backward_subset_subsumed:           1
% 23.77/3.51  res_forward_subsumed:                   0
% 23.77/3.51  res_backward_subsumed:                  2
% 23.77/3.51  res_forward_subsumption_resolution:     8
% 23.77/3.51  res_backward_subsumption_resolution:    9
% 23.77/3.51  res_clause_to_clause_subsumption:       6738
% 23.77/3.51  res_orphan_elimination:                 0
% 23.77/3.51  res_tautology_del:                      234
% 23.77/3.51  res_num_eq_res_simplified:              0
% 23.77/3.51  res_num_sel_changes:                    0
% 23.77/3.51  res_moves_from_active_to_pass:          0
% 23.77/3.51  
% 23.77/3.51  ------ Superposition
% 23.77/3.51  
% 23.77/3.51  sup_time_total:                         0.
% 23.77/3.51  sup_time_generating:                    0.
% 23.77/3.51  sup_time_sim_full:                      0.
% 23.77/3.51  sup_time_sim_immed:                     0.
% 23.77/3.51  
% 23.77/3.51  sup_num_of_clauses:                     1432
% 23.77/3.51  sup_num_in_active:                      346
% 23.77/3.51  sup_num_in_passive:                     1086
% 23.77/3.51  sup_num_of_loops:                       400
% 23.77/3.51  sup_fw_superposition:                   814
% 23.77/3.51  sup_bw_superposition:                   1358
% 23.77/3.51  sup_immediate_simplified:               932
% 23.77/3.51  sup_given_eliminated:                   17
% 23.77/3.51  comparisons_done:                       0
% 23.77/3.51  comparisons_avoided:                    369
% 23.77/3.51  
% 23.77/3.51  ------ Simplifications
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  sim_fw_subset_subsumed:                 275
% 23.77/3.51  sim_bw_subset_subsumed:                 29
% 23.77/3.51  sim_fw_subsumed:                        341
% 23.77/3.51  sim_bw_subsumed:                        62
% 23.77/3.51  sim_fw_subsumption_res:                 0
% 23.77/3.51  sim_bw_subsumption_res:                 0
% 23.77/3.51  sim_tautology_del:                      37
% 23.77/3.51  sim_eq_tautology_del:                   22
% 23.77/3.51  sim_eq_res_simp:                        0
% 23.77/3.51  sim_fw_demodulated:                     70
% 23.77/3.51  sim_bw_demodulated:                     30
% 23.77/3.51  sim_light_normalised:                   764
% 23.77/3.51  sim_joinable_taut:                      0
% 23.77/3.51  sim_joinable_simp:                      0
% 23.77/3.51  sim_ac_normalised:                      0
% 23.77/3.51  sim_smt_subsumption:                    0
% 23.77/3.51  
%------------------------------------------------------------------------------
