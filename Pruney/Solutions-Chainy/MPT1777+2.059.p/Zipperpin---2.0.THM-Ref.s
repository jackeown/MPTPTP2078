%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xR1HJZY1n5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 244 expanded)
%              Number of leaves         :   42 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          : 1251 (6940 expanded)
%              Number of equality atoms :   15 ( 171 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X32 )
      | ( X32 != X30 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_hidden @ X32 @ X29 )
      | ~ ( v3_pre_topc @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v3_pre_topc @ X29 @ X26 )
      | ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,(
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
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('30',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
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
    inference(demod,[status(thm)],['21','22','23','24','25','28','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('57',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['49','54','55','56'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('61',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','62'])).

thf('64',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('72',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','75','76'])).

thf('78',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('80',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xR1HJZY1n5
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 506 iterations in 0.323s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.59/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.78  thf(sk_G_type, type, sk_G: $i).
% 0.59/0.78  thf(sk_F_type, type, sk_F: $i).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.59/0.78  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.59/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.78  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.59/0.78  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.78  thf(t88_tmap_1, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.78             ( l1_pre_topc @ B ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78               ( ![D:$i]:
% 0.59/0.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.78                   ( ![E:$i]:
% 0.59/0.78                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.78                         ( v1_funct_2 @
% 0.59/0.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.78                         ( m1_subset_1 @
% 0.59/0.78                           E @ 
% 0.59/0.78                           ( k1_zfmisc_1 @
% 0.59/0.78                             ( k2_zfmisc_1 @
% 0.59/0.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.78                       ( ( ( g1_pre_topc @
% 0.59/0.78                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.59/0.78                           ( D ) ) =>
% 0.59/0.78                         ( ![F:$i]:
% 0.59/0.78                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.59/0.78                             ( ![G:$i]:
% 0.59/0.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.59/0.78                                 ( ( ( ( F ) = ( G ) ) & 
% 0.59/0.78                                     ( r1_tmap_1 @
% 0.59/0.78                                       C @ B @ 
% 0.59/0.78                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.59/0.78                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.78            ( l1_pre_topc @ A ) ) =>
% 0.59/0.78          ( ![B:$i]:
% 0.59/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.78                ( l1_pre_topc @ B ) ) =>
% 0.59/0.78              ( ![C:$i]:
% 0.59/0.78                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78                  ( ![D:$i]:
% 0.59/0.78                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.78                      ( ![E:$i]:
% 0.59/0.78                        ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.78                            ( v1_funct_2 @
% 0.59/0.78                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.78                            ( m1_subset_1 @
% 0.59/0.78                              E @ 
% 0.59/0.78                              ( k1_zfmisc_1 @
% 0.59/0.78                                ( k2_zfmisc_1 @
% 0.59/0.78                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.78                          ( ( ( g1_pre_topc @
% 0.59/0.78                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.59/0.78                              ( D ) ) =>
% 0.59/0.78                            ( ![F:$i]:
% 0.59/0.78                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.59/0.78                                ( ![G:$i]:
% 0.59/0.78                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.59/0.78                                    ( ( ( ( F ) = ( G ) ) & 
% 0.59/0.78                                        ( r1_tmap_1 @
% 0.59/0.78                                          C @ B @ 
% 0.59/0.78                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.59/0.78                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.59/0.78  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(fc10_tops_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X16 : $i]:
% 0.59/0.78         ((v3_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.59/0.78          | ~ (l1_pre_topc @ X16)
% 0.59/0.78          | ~ (v2_pre_topc @ X16))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.59/0.78  thf(d3_struct_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X9 : $i]:
% 0.59/0.78         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.78  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t2_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ A @ B ) =>
% 0.59/0.78       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X2 : $i, X3 : $i]:
% 0.59/0.78         ((r2_hidden @ X2 @ X3)
% 0.59/0.78          | (v1_xboole_0 @ X3)
% 0.59/0.78          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.78  thf(dt_k2_subset_1, axiom,
% 0.59/0.78    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.59/0.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.59/0.78  thf('7', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.59/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.59/0.78  thf('8', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('10', plain, (((sk_F) = (sk_G))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.59/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ 
% 0.59/0.78        (k1_zfmisc_1 @ 
% 0.59/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t84_tmap_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.78             ( l1_pre_topc @ B ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78               ( ![D:$i]:
% 0.59/0.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.78                   ( ![E:$i]:
% 0.59/0.78                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.78                         ( v1_funct_2 @
% 0.59/0.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.78                         ( m1_subset_1 @
% 0.59/0.78                           E @ 
% 0.59/0.78                           ( k1_zfmisc_1 @
% 0.59/0.78                             ( k2_zfmisc_1 @
% 0.59/0.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.78                       ( ( m1_pre_topc @ C @ D ) =>
% 0.59/0.78                         ( ![F:$i]:
% 0.59/0.78                           ( ( m1_subset_1 @
% 0.59/0.78                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.59/0.78                             ( ![G:$i]:
% 0.59/0.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.59/0.78                                 ( ![H:$i]:
% 0.59/0.78                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.59/0.78                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.59/0.78                                         ( r2_hidden @ G @ F ) & 
% 0.59/0.78                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.59/0.78                                         ( ( G ) = ( H ) ) ) =>
% 0.59/0.78                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.59/0.78                                         ( r1_tmap_1 @
% 0.59/0.78                                           C @ B @ 
% 0.59/0.78                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.59/0.78                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 0.59/0.78         X32 : $i]:
% 0.59/0.78         ((v2_struct_0 @ X25)
% 0.59/0.78          | ~ (v2_pre_topc @ X25)
% 0.59/0.78          | ~ (l1_pre_topc @ X25)
% 0.59/0.78          | (v2_struct_0 @ X26)
% 0.59/0.78          | ~ (m1_pre_topc @ X26 @ X27)
% 0.59/0.78          | ~ (m1_pre_topc @ X28 @ X26)
% 0.59/0.78          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.59/0.78          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.59/0.78          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.59/0.78               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.59/0.78          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X32)
% 0.59/0.78          | ((X32) != (X30))
% 0.59/0.78          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.59/0.78          | ~ (r2_hidden @ X32 @ X29)
% 0.59/0.78          | ~ (v3_pre_topc @ X29 @ X26)
% 0.59/0.78          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X26))
% 0.59/0.78          | ~ (m1_subset_1 @ X31 @ 
% 0.59/0.78               (k1_zfmisc_1 @ 
% 0.59/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.59/0.78          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.59/0.78          | ~ (v1_funct_1 @ X31)
% 0.59/0.78          | ~ (m1_pre_topc @ X28 @ X27)
% 0.59/0.78          | (v2_struct_0 @ X28)
% 0.59/0.78          | ~ (l1_pre_topc @ X27)
% 0.59/0.78          | ~ (v2_pre_topc @ X27)
% 0.59/0.78          | (v2_struct_0 @ X27))),
% 0.59/0.78      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.78         ((v2_struct_0 @ X27)
% 0.59/0.78          | ~ (v2_pre_topc @ X27)
% 0.59/0.78          | ~ (l1_pre_topc @ X27)
% 0.59/0.78          | (v2_struct_0 @ X28)
% 0.59/0.78          | ~ (m1_pre_topc @ X28 @ X27)
% 0.59/0.78          | ~ (v1_funct_1 @ X31)
% 0.59/0.78          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.59/0.78          | ~ (m1_subset_1 @ X31 @ 
% 0.59/0.78               (k1_zfmisc_1 @ 
% 0.59/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.59/0.78          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.59/0.78          | ~ (v3_pre_topc @ X29 @ X26)
% 0.59/0.78          | ~ (r2_hidden @ X30 @ X29)
% 0.59/0.78          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.59/0.78          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.59/0.78          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.59/0.78               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.59/0.78          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.59/0.78          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.59/0.78          | ~ (m1_pre_topc @ X28 @ X26)
% 0.59/0.78          | ~ (m1_pre_topc @ X26 @ X27)
% 0.59/0.78          | (v2_struct_0 @ X26)
% 0.59/0.78          | ~ (l1_pre_topc @ X25)
% 0.59/0.78          | ~ (v2_pre_topc @ X25)
% 0.59/0.78          | (v2_struct_0 @ X25))),
% 0.59/0.78      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.78         ((v2_struct_0 @ sk_B)
% 0.59/0.78          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.78          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.78          | (v2_struct_0 @ sk_D)
% 0.59/0.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.59/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.59/0.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.59/0.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.59/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.59/0.78          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.59/0.78          | ~ (r2_hidden @ X3 @ X2)
% 0.59/0.78          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.59/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.59/0.78          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.78          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.78          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.78          | (v2_struct_0 @ X1)
% 0.59/0.78          | ~ (l1_pre_topc @ X0)
% 0.59/0.78          | ~ (v2_pre_topc @ X0)
% 0.59/0.78          | (v2_struct_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['12', '14'])).
% 0.59/0.78  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.78         ((v2_struct_0 @ sk_B)
% 0.59/0.78          | (v2_struct_0 @ sk_D)
% 0.59/0.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.59/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.59/0.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.59/0.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.59/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.59/0.78          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.59/0.78          | ~ (r2_hidden @ X3 @ X2)
% 0.59/0.78          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.59/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.59/0.78          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.78          | (v2_struct_0 @ X1)
% 0.59/0.78          | ~ (l1_pre_topc @ X0)
% 0.59/0.78          | ~ (v2_pre_topc @ X0)
% 0.59/0.78          | (v2_struct_0 @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v2_struct_0 @ sk_A)
% 0.59/0.78          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_C)
% 0.59/0.78          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.59/0.78          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.59/0.78          | ~ (r2_hidden @ sk_F @ X0)
% 0.59/0.78          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.59/0.78          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.59/0.78          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_D)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '20'])).
% 0.59/0.78  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('25', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('26', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('27', plain, (((sk_F) = (sk_G))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('28', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.59/0.78      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t2_tsep_1, axiom,
% 0.59/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.78  thf(t65_pre_topc, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_pre_topc @ A ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( l1_pre_topc @ B ) =>
% 0.59/0.78           ( ( m1_pre_topc @ A @ B ) <=>
% 0.59/0.78             ( m1_pre_topc @
% 0.59/0.78               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X14 : $i, X15 : $i]:
% 0.59/0.78         (~ (l1_pre_topc @ X14)
% 0.59/0.78          | ~ (m1_pre_topc @ X15 @ X14)
% 0.59/0.78          | (m1_pre_topc @ X15 @ 
% 0.59/0.78             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.59/0.78          | ~ (l1_pre_topc @ X15))),
% 0.59/0.78      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (l1_pre_topc @ X0)
% 0.59/0.78          | ~ (l1_pre_topc @ X0)
% 0.59/0.78          | (m1_pre_topc @ X0 @ 
% 0.59/0.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.59/0.78          | ~ (l1_pre_topc @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((m1_pre_topc @ X0 @ 
% 0.59/0.78           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.59/0.78          | ~ (l1_pre_topc @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.59/0.78  thf('34', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.59/0.78      inference('sup+', [status(thm)], ['29', '33'])).
% 0.59/0.78  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_m1_pre_topc, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_pre_topc @ A ) =>
% 0.59/0.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X11 : $i, X12 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X11 @ X12)
% 0.59/0.78          | (l1_pre_topc @ X11)
% 0.59/0.78          | ~ (l1_pre_topc @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.78  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.78  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.78      inference('demod', [status(thm)], ['34', '39'])).
% 0.59/0.78  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v2_struct_0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_C)
% 0.59/0.78          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.59/0.78          | ~ (r2_hidden @ sk_F @ X0)
% 0.59/0.78          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.59/0.78          | (v2_struct_0 @ sk_D)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['21', '22', '23', '24', '25', '28', '40', '41'])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['8', '42'])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X14 : $i, X15 : $i]:
% 0.59/0.78         (~ (l1_pre_topc @ X14)
% 0.59/0.78          | ~ (m1_pre_topc @ X15 @ 
% 0.59/0.78               (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.59/0.78          | (m1_pre_topc @ X15 @ X14)
% 0.59/0.78          | ~ (l1_pre_topc @ X15))),
% 0.59/0.78      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (l1_pre_topc @ 
% 0.59/0.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.59/0.78          | ~ (l1_pre_topc @ 
% 0.59/0.78               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.59/0.78          | (m1_pre_topc @ 
% 0.59/0.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.59/0.78          | ~ (l1_pre_topc @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (l1_pre_topc @ X0)
% 0.59/0.78          | (m1_pre_topc @ 
% 0.59/0.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.59/0.78          | ~ (l1_pre_topc @ 
% 0.59/0.78               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['47'])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      ((~ (l1_pre_topc @ sk_D)
% 0.59/0.78        | (m1_pre_topc @ 
% 0.59/0.78           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['44', '48'])).
% 0.59/0.78  thf('50', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (![X11 : $i, X12 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X11 @ X12)
% 0.59/0.78          | (l1_pre_topc @ X11)
% 0.59/0.78          | ~ (l1_pre_topc @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.78  thf('52', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.78  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('56', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.78  thf('57', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.59/0.78      inference('demod', [status(thm)], ['49', '54', '55', '56'])).
% 0.59/0.78  thf(t35_borsuk_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_pre_topc @ A ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_pre_topc @ B @ A ) =>
% 0.59/0.78           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.59/0.78  thf('58', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.78          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.59/0.78          | ~ (l1_pre_topc @ X21))),
% 0.59/0.78      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.59/0.78  thf('59', plain,
% 0.59/0.78      ((~ (l1_pre_topc @ sk_C)
% 0.59/0.78        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.78  thf('60', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.78  thf('61', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.59/0.78      inference('demod', [status(thm)], ['59', '60'])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['43', '61'])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['5', '62'])).
% 0.59/0.78  thf('64', plain,
% 0.59/0.78      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.59/0.78        | ~ (l1_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['2', '63'])).
% 0.59/0.78  thf('65', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf(dt_l1_pre_topc, axiom,
% 0.59/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.78  thf('67', plain, ((l1_struct_0 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.59/0.78      inference('demod', [status(thm)], ['64', '67'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      ((~ (v2_pre_topc @ sk_D)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '68'])).
% 0.59/0.78  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc1_pre_topc, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.59/0.78  thf('71', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X7 @ X8)
% 0.59/0.78          | (v2_pre_topc @ X7)
% 0.59/0.78          | ~ (l1_pre_topc @ X8)
% 0.59/0.78          | ~ (v2_pre_topc @ X8))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.59/0.78  thf('72', plain,
% 0.59/0.78      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.78  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('75', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.78      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.59/0.78  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf('77', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '75', '76'])).
% 0.59/0.78  thf('78', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('79', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.78  thf(fc2_struct_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.78       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.78  thf('80', plain,
% 0.59/0.78      (![X13 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.59/0.78          | ~ (l1_struct_0 @ X13)
% 0.59/0.78          | (v2_struct_0 @ X13))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.78  thf('81', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | ~ (l1_struct_0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.78  thf('82', plain, ((l1_struct_0 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.78  thf('83', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D))),
% 0.59/0.78      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.78  thf('84', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_D)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('85', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('86', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.78  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('88', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('clc', [status(thm)], ['86', '87'])).
% 0.59/0.78  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('90', plain, ((v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('clc', [status(thm)], ['88', '89'])).
% 0.59/0.78  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
