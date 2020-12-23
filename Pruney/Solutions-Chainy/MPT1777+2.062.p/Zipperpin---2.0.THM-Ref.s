%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8s9xelj88

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:36 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 277 expanded)
%              Number of leaves         :   43 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          : 1255 (7578 expanded)
%              Number of equality atoms :   16 ( 190 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t88_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                          = D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                 => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                            = D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                   => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tmap_1 @ X25 @ X22 @ ( k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28 ) @ X27 )
      | ( r1_tmap_1 @ X23 @ X22 @ X28 @ X29 )
      | ( X29 != X27 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r1_tmap_1 @ X23 @ X22 @ X28 @ X27 )
      | ~ ( r1_tmap_1 @ X25 @ X22 @ ( k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','26','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['48','53'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('58',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','59'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('73',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','75','76'])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('80',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('83',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('84',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','87','88'])).

thf('90',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8s9xelj88
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 247 iterations in 0.157s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(t88_tmap_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.56             ( l1_pre_topc @ B ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.56               ( ![D:$i]:
% 0.37/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.56                   ( ![E:$i]:
% 0.37/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.56                         ( v1_funct_2 @
% 0.37/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.56                         ( m1_subset_1 @
% 0.37/0.56                           E @ 
% 0.37/0.56                           ( k1_zfmisc_1 @
% 0.37/0.56                             ( k2_zfmisc_1 @
% 0.37/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.56                       ( ( ( g1_pre_topc @
% 0.37/0.56                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.37/0.56                           ( D ) ) =>
% 0.37/0.56                         ( ![F:$i]:
% 0.37/0.56                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.56                             ( ![G:$i]:
% 0.37/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.56                                 ( ( ( ( F ) = ( G ) ) & 
% 0.37/0.56                                     ( r1_tmap_1 @
% 0.37/0.56                                       C @ B @ 
% 0.37/0.56                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.37/0.56                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.56                ( l1_pre_topc @ B ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.56                  ( ![D:$i]:
% 0.37/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.56                      ( ![E:$i]:
% 0.37/0.56                        ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.56                            ( v1_funct_2 @
% 0.37/0.56                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.56                            ( m1_subset_1 @
% 0.37/0.56                              E @ 
% 0.37/0.56                              ( k1_zfmisc_1 @
% 0.37/0.56                                ( k2_zfmisc_1 @
% 0.37/0.56                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.56                          ( ( ( g1_pre_topc @
% 0.37/0.56                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.37/0.56                              ( D ) ) =>
% 0.37/0.56                            ( ![F:$i]:
% 0.37/0.56                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.56                                ( ![G:$i]:
% 0.37/0.56                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.56                                    ( ( ( ( F ) = ( G ) ) & 
% 0.37/0.56                                        ( r1_tmap_1 @
% 0.37/0.56                                          C @ B @ 
% 0.37/0.56                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.37/0.56                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.37/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(fc10_tops_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X15 : $i]:
% 0.37/0.56         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.37/0.56          | ~ (l1_pre_topc @ X15)
% 0.37/0.56          | ~ (v2_pre_topc @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.37/0.56  thf(d3_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X6 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X6 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf(dt_k2_subset_1, axiom,
% 0.37/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.56  thf('5', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.56  thf('6', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain, (((sk_F) = (sk_G))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_E @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t84_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.56             ( l1_pre_topc @ B ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.56               ( ![D:$i]:
% 0.37/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.56                   ( ![E:$i]:
% 0.37/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.56                         ( v1_funct_2 @
% 0.37/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.56                         ( m1_subset_1 @
% 0.37/0.56                           E @ 
% 0.37/0.56                           ( k1_zfmisc_1 @
% 0.37/0.56                             ( k2_zfmisc_1 @
% 0.37/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.37/0.56                         ( ![F:$i]:
% 0.37/0.56                           ( ( m1_subset_1 @
% 0.37/0.56                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.37/0.56                             ( ![G:$i]:
% 0.37/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.56                                 ( ![H:$i]:
% 0.37/0.56                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.56                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.37/0.56                                         ( r2_hidden @ G @ F ) & 
% 0.37/0.56                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.37/0.56                                         ( ( G ) = ( H ) ) ) =>
% 0.37/0.56                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.37/0.56                                         ( r1_tmap_1 @
% 0.37/0.56                                           C @ B @ 
% 0.37/0.56                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.37/0.56                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 0.37/0.56         X29 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X22)
% 0.37/0.56          | ~ (v2_pre_topc @ X22)
% 0.37/0.56          | ~ (l1_pre_topc @ X22)
% 0.37/0.56          | (v2_struct_0 @ X23)
% 0.37/0.56          | ~ (m1_pre_topc @ X23 @ X24)
% 0.37/0.56          | ~ (m1_pre_topc @ X25 @ X23)
% 0.37/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.56          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.37/0.56          | ~ (r1_tmap_1 @ X25 @ X22 @ 
% 0.37/0.56               (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.37/0.56          | (r1_tmap_1 @ X23 @ X22 @ X28 @ X29)
% 0.37/0.56          | ((X29) != (X27))
% 0.37/0.56          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.56          | ~ (r2_hidden @ X29 @ X26)
% 0.37/0.56          | ~ (v3_pre_topc @ X26 @ X23)
% 0.37/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X23))
% 0.37/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.37/0.56          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.37/0.56          | ~ (v1_funct_1 @ X28)
% 0.37/0.56          | ~ (m1_pre_topc @ X25 @ X24)
% 0.37/0.56          | (v2_struct_0 @ X25)
% 0.37/0.56          | ~ (l1_pre_topc @ X24)
% 0.37/0.56          | ~ (v2_pre_topc @ X24)
% 0.37/0.56          | (v2_struct_0 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X24)
% 0.37/0.56          | ~ (v2_pre_topc @ X24)
% 0.37/0.56          | ~ (l1_pre_topc @ X24)
% 0.37/0.56          | (v2_struct_0 @ X25)
% 0.37/0.56          | ~ (m1_pre_topc @ X25 @ X24)
% 0.37/0.56          | ~ (v1_funct_1 @ X28)
% 0.37/0.56          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.37/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.37/0.56          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.37/0.56          | ~ (v3_pre_topc @ X26 @ X23)
% 0.37/0.56          | ~ (r2_hidden @ X27 @ X26)
% 0.37/0.56          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.56          | (r1_tmap_1 @ X23 @ X22 @ X28 @ X27)
% 0.37/0.56          | ~ (r1_tmap_1 @ X25 @ X22 @ 
% 0.37/0.56               (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.37/0.56          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.37/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.56          | ~ (m1_pre_topc @ X25 @ X23)
% 0.37/0.56          | ~ (m1_pre_topc @ X23 @ X24)
% 0.37/0.56          | (v2_struct_0 @ X23)
% 0.37/0.56          | ~ (l1_pre_topc @ X22)
% 0.37/0.56          | ~ (v2_pre_topc @ X22)
% 0.37/0.56          | (v2_struct_0 @ X22))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_B)
% 0.37/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_D)
% 0.37/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.37/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.37/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.56          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.37/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.37/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X1)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (v2_pre_topc @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.56  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_D)
% 0.37/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.37/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.37/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.56          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.37/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X1)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (v2_pre_topc @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_C)
% 0.37/0.56          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.37/0.56          | ~ (r2_hidden @ sk_F @ X0)
% 0.37/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.37/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.56          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.37/0.56          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_D)
% 0.37/0.56          | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '18'])).
% 0.37/0.56  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('25', plain, (((sk_F) = (sk_G))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t2_tsep_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.56  thf(t65_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( l1_pre_topc @ B ) =>
% 0.37/0.56           ( ( m1_pre_topc @ A @ B ) <=>
% 0.37/0.56             ( m1_pre_topc @
% 0.37/0.56               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (m1_pre_topc @ X14 @ X13)
% 0.37/0.56          | (m1_pre_topc @ X14 @ 
% 0.37/0.56             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.37/0.56          | ~ (l1_pre_topc @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | (m1_pre_topc @ X0 @ 
% 0.37/0.56             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_pre_topc @ X0 @ 
% 0.37/0.56           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.56  thf('32', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '31'])).
% 0.37/0.56  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_m1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '37'])).
% 0.37/0.56  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_C)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.37/0.56          | ~ (r2_hidden @ sk_F @ X0)
% 0.37/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.37/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.56          | (v2_struct_0 @ sk_D)
% 0.37/0.56          | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)],
% 0.37/0.56                ['19', '20', '21', '22', '23', '26', '38', '39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.37/0.56        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.37/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_C)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t59_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @
% 0.37/0.56             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.37/0.56           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X11 @ 
% 0.37/0.56             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.37/0.56          | (m1_pre_topc @ X11 @ X12)
% 0.37/0.56          | ~ (l1_pre_topc @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_C)
% 0.37/0.56          | (m1_pre_topc @ X0 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.56  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['42', '47'])).
% 0.37/0.56  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('51', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.56  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['48', '53'])).
% 0.37/0.56  thf(t35_borsuk_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X17 @ X18)
% 0.37/0.56          | (r1_tarski @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.37/0.56          | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_C)
% 0.37/0.56        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain, ((l1_pre_topc @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('58', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.37/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_C)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '58'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_C)
% 0.37/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.37/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X6 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('62', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t2_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         ((r2_hidden @ X2 @ X3)
% 0.37/0.56          | (v1_xboole_0 @ X3)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.37/0.56        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['61', '64'])).
% 0.37/0.56  thf('66', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.56  thf(dt_l1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.56  thf('67', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('68', plain, ((l1_struct_0 @ sk_D)),
% 0.37/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['65', '68'])).
% 0.37/0.56  thf(fc2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (![X10 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.37/0.56          | ~ (l1_struct_0 @ X10)
% 0.37/0.56          | (v2_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.56  thf('72', plain, ((l1_struct_0 @ sk_D)),
% 0.37/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D)) | (v2_struct_0 @ sk_D))),
% 0.37/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('75', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))),
% 0.37/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.37/0.57  thf('76', plain, ((l1_struct_0 @ sk_D)),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.37/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['60', '75', '76'])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.37/0.57        | ~ (l1_struct_0 @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_B)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '77'])).
% 0.37/0.57  thf('79', plain, ((l1_struct_0 @ sk_D)),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.57  thf('80', plain,
% 0.37/0.57      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_B)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.57  thf('81', plain,
% 0.37/0.57      ((~ (v2_pre_topc @ sk_D)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '80'])).
% 0.37/0.57  thf('82', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc1_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.37/0.57  thf('83', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X4 @ X5)
% 0.37/0.57          | (v2_pre_topc @ X4)
% 0.37/0.57          | ~ (l1_pre_topc @ X5)
% 0.37/0.57          | ~ (v2_pre_topc @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.37/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.57  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('87', plain, ((v2_pre_topc @ sk_D)),
% 0.37/0.57      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.37/0.57  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('89', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['81', '87', '88'])).
% 0.37/0.57  thf('90', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('91', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_B)
% 0.37/0.57        | (v2_struct_0 @ sk_D)
% 0.37/0.57        | (v2_struct_0 @ sk_C)
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.57  thf('92', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('93', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['91', '92'])).
% 0.37/0.57  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('95', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.37/0.57      inference('clc', [status(thm)], ['93', '94'])).
% 0.37/0.57  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('97', plain, ((v2_struct_0 @ sk_C)),
% 0.37/0.57      inference('clc', [status(thm)], ['95', '96'])).
% 0.37/0.57  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
