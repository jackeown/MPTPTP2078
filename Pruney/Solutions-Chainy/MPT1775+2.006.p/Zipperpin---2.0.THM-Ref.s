%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BwiAIeNpM5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:21 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 642 expanded)
%              Number of leaves         :   35 ( 193 expanded)
%              Depth                    :   32
%              Number of atoms          : 2374 (22433 expanded)
%              Number of equality atoms :   14 ( 294 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t86_tmap_1,conjecture,(
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
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('23',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('33',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
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

thf('36',plain,(
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

thf('37',plain,(
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
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49','50','51'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['31','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['59','60','61','62','68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['53','55','69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['22','70'])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['13'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('81',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('82',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('94',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['17','21','92','93'])).

thf('95',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['8','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('97',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tmap_1 @ X23 @ X22 @ X28 @ X29 )
      | ( r1_tmap_1 @ X25 @ X22 @ ( k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28 ) @ X27 )
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

thf('100',plain,(
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
      | ( r1_tmap_1 @ X25 @ X22 @ ( k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28 ) @ X27 )
      | ~ ( r1_tmap_1 @ X23 @ X22 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
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
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['59','60','61','62','68'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','117'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('124',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('126',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['17','21','92','126'])).

thf('128',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['123','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['80','81'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BwiAIeNpM5
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:14:25 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.33/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.54  % Solved by: fo/fo7.sh
% 0.33/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.54  % done 99 iterations in 0.050s
% 0.33/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.54  % SZS output start Refutation
% 0.33/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.33/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.33/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.33/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.33/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.33/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.33/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.33/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.33/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.33/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.33/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.33/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.33/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.33/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.33/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.33/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.33/0.54  thf(t86_tmap_1, conjecture,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54             ( l1_pre_topc @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.33/0.54               ( ![D:$i]:
% 0.33/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.33/0.54                   ( ![E:$i]:
% 0.33/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.33/0.54                         ( v1_funct_2 @
% 0.33/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                         ( m1_subset_1 @
% 0.33/0.54                           E @ 
% 0.33/0.54                           ( k1_zfmisc_1 @
% 0.33/0.54                             ( k2_zfmisc_1 @
% 0.33/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.33/0.54                         ( ![F:$i]:
% 0.33/0.54                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                             ( ![G:$i]:
% 0.33/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.33/0.54                                 ( ( ( F ) = ( G ) ) =>
% 0.33/0.54                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.33/0.54                                     ( r1_tmap_1 @
% 0.33/0.54                                       C @ B @ 
% 0.33/0.54                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.54    (~( ![A:$i]:
% 0.33/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.33/0.54            ( l1_pre_topc @ A ) ) =>
% 0.33/0.54          ( ![B:$i]:
% 0.33/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54                ( l1_pre_topc @ B ) ) =>
% 0.33/0.54              ( ![C:$i]:
% 0.33/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.33/0.54                  ( ![D:$i]:
% 0.33/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.33/0.54                      ( ![E:$i]:
% 0.33/0.54                        ( ( ( v1_funct_1 @ E ) & 
% 0.33/0.54                            ( v1_funct_2 @
% 0.33/0.54                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                            ( m1_subset_1 @
% 0.33/0.54                              E @ 
% 0.33/0.54                              ( k1_zfmisc_1 @
% 0.33/0.54                                ( k2_zfmisc_1 @
% 0.33/0.54                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.33/0.54                            ( ![F:$i]:
% 0.33/0.54                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                                ( ![G:$i]:
% 0.33/0.54                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.33/0.54                                    ( ( ( F ) = ( G ) ) =>
% 0.33/0.54                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.33/0.54                                        ( r1_tmap_1 @
% 0.33/0.54                                          C @ B @ 
% 0.33/0.54                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.33/0.54    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.33/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('3', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.33/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.33/0.54  thf(t2_subset, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.33/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.33/0.54  thf('5', plain,
% 0.33/0.54      (![X3 : $i, X4 : $i]:
% 0.33/0.54         ((r2_hidden @ X3 @ X4)
% 0.33/0.54          | (v1_xboole_0 @ X4)
% 0.33/0.54          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.33/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.33/0.54  thf('6', plain,
% 0.33/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.33/0.54        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.54  thf('7', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('8', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.33/0.54      inference('split', [status(esa)], ['7'])).
% 0.33/0.54  thf('9', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('10', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('11', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.33/0.54        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.33/0.54  thf('12', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.33/0.54      inference('split', [status(esa)], ['11'])).
% 0.33/0.54  thf('13', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('14', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['13'])).
% 0.33/0.54  thf('15', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('16', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.54  thf('17', plain,
% 0.33/0.54      (~
% 0.33/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.33/0.54      inference('sup-', [status(thm)], ['12', '16'])).
% 0.33/0.54  thf('18', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('19', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('20', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.33/0.54  thf('21', plain,
% 0.33/0.54      (~
% 0.33/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.33/0.54       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('split', [status(esa)], ['20'])).
% 0.33/0.54  thf('22', plain,
% 0.33/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.33/0.54        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.54  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t1_tsep_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_pre_topc @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.54           ( m1_subset_1 @
% 0.33/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.33/0.54  thf('24', plain,
% 0.33/0.54      (![X17 : $i, X18 : $i]:
% 0.33/0.54         (~ (m1_pre_topc @ X17 @ X18)
% 0.33/0.54          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.33/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.33/0.54          | ~ (l1_pre_topc @ X18))),
% 0.33/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.33/0.54  thf('25', plain,
% 0.33/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.33/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.33/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.33/0.54  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(dt_m1_pre_topc, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_pre_topc @ A ) =>
% 0.33/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.33/0.54  thf('27', plain,
% 0.33/0.54      (![X11 : $i, X12 : $i]:
% 0.33/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.33/0.54          | (l1_pre_topc @ X11)
% 0.33/0.54          | ~ (l1_pre_topc @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.33/0.54  thf('28', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.33/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.33/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('30', plain, ((l1_pre_topc @ sk_D)),
% 0.33/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.33/0.54  thf('31', plain,
% 0.33/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.33/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.33/0.54      inference('demod', [status(thm)], ['25', '30'])).
% 0.33/0.54  thf('32', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['7'])).
% 0.33/0.54  thf('33', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('34', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.33/0.54  thf('35', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t84_tmap_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54             ( l1_pre_topc @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.33/0.54               ( ![D:$i]:
% 0.33/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.33/0.54                   ( ![E:$i]:
% 0.33/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.33/0.54                         ( v1_funct_2 @
% 0.33/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.33/0.54                         ( m1_subset_1 @
% 0.33/0.54                           E @ 
% 0.33/0.54                           ( k1_zfmisc_1 @
% 0.33/0.54                             ( k2_zfmisc_1 @
% 0.33/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.33/0.54                       ( ( m1_pre_topc @ C @ D ) =>
% 0.33/0.54                         ( ![F:$i]:
% 0.33/0.54                           ( ( m1_subset_1 @
% 0.33/0.54                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.33/0.54                             ( ![G:$i]:
% 0.33/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                                 ( ![H:$i]:
% 0.33/0.54                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.33/0.54                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.33/0.54                                         ( r2_hidden @ G @ F ) & 
% 0.33/0.54                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.33/0.54                                         ( ( G ) = ( H ) ) ) =>
% 0.33/0.54                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.33/0.54                                         ( r1_tmap_1 @
% 0.33/0.54                                           C @ B @ 
% 0.33/0.54                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.33/0.54                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('36', plain,
% 0.33/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 0.33/0.54         X29 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X22)
% 0.33/0.54          | ~ (v2_pre_topc @ X22)
% 0.33/0.54          | ~ (l1_pre_topc @ X22)
% 0.33/0.54          | (v2_struct_0 @ X23)
% 0.33/0.54          | ~ (m1_pre_topc @ X23 @ X24)
% 0.33/0.54          | ~ (m1_pre_topc @ X25 @ X23)
% 0.33/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.33/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.33/0.54          | ~ (r1_tmap_1 @ X25 @ X22 @ 
% 0.33/0.54               (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.33/0.54          | (r1_tmap_1 @ X23 @ X22 @ X28 @ X29)
% 0.33/0.54          | ((X29) != (X27))
% 0.33/0.54          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.33/0.54          | ~ (r2_hidden @ X29 @ X26)
% 0.33/0.54          | ~ (v3_pre_topc @ X26 @ X23)
% 0.33/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X23))
% 0.33/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.33/0.54          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.33/0.54          | ~ (v1_funct_1 @ X28)
% 0.33/0.54          | ~ (m1_pre_topc @ X25 @ X24)
% 0.33/0.54          | (v2_struct_0 @ X25)
% 0.33/0.54          | ~ (l1_pre_topc @ X24)
% 0.33/0.54          | ~ (v2_pre_topc @ X24)
% 0.33/0.54          | (v2_struct_0 @ X24))),
% 0.33/0.54      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.33/0.54  thf('37', plain,
% 0.33/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X24)
% 0.33/0.54          | ~ (v2_pre_topc @ X24)
% 0.33/0.54          | ~ (l1_pre_topc @ X24)
% 0.33/0.54          | (v2_struct_0 @ X25)
% 0.33/0.54          | ~ (m1_pre_topc @ X25 @ X24)
% 0.33/0.54          | ~ (v1_funct_1 @ X28)
% 0.33/0.54          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.33/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.33/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.33/0.54          | ~ (v3_pre_topc @ X26 @ X23)
% 0.33/0.54          | ~ (r2_hidden @ X27 @ X26)
% 0.33/0.54          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.33/0.54          | (r1_tmap_1 @ X23 @ X22 @ X28 @ X27)
% 0.33/0.54          | ~ (r1_tmap_1 @ X25 @ X22 @ 
% 0.33/0.54               (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.33/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.33/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.33/0.54          | ~ (m1_pre_topc @ X25 @ X23)
% 0.33/0.54          | ~ (m1_pre_topc @ X23 @ X24)
% 0.33/0.54          | (v2_struct_0 @ X23)
% 0.33/0.54          | ~ (l1_pre_topc @ X22)
% 0.33/0.54          | ~ (v2_pre_topc @ X22)
% 0.33/0.54          | (v2_struct_0 @ X22))),
% 0.33/0.54      inference('simplify', [status(thm)], ['36'])).
% 0.33/0.54  thf('38', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ sk_D)
% 0.33/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.33/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.33/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.33/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.33/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.33/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.33/0.54          | ~ (r2_hidden @ X3 @ X2)
% 0.33/0.54          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.33/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.33/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.33/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.33/0.54          | (v2_struct_0 @ X1)
% 0.33/0.54          | ~ (l1_pre_topc @ X0)
% 0.33/0.54          | ~ (v2_pre_topc @ X0)
% 0.33/0.54          | (v2_struct_0 @ X0))),
% 0.33/0.54      inference('sup-', [status(thm)], ['35', '37'])).
% 0.33/0.54  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('41', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('43', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ sk_D)
% 0.33/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.33/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.33/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.33/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.33/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.33/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.33/0.54          | ~ (r2_hidden @ X3 @ X2)
% 0.33/0.54          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.33/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.33/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.33/0.54          | (v2_struct_0 @ X1)
% 0.33/0.54          | ~ (l1_pre_topc @ X0)
% 0.33/0.54          | ~ (v2_pre_topc @ X0)
% 0.33/0.54          | (v2_struct_0 @ X0))),
% 0.33/0.54      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.33/0.54  thf('44', plain,
% 0.33/0.54      ((![X0 : $i]:
% 0.33/0.54          ((v2_struct_0 @ sk_A)
% 0.33/0.54           | ~ (v2_pre_topc @ sk_A)
% 0.33/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.33/0.54           | (v2_struct_0 @ sk_C)
% 0.33/0.54           | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.33/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.33/0.54           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.33/0.54           | ~ (r2_hidden @ sk_F @ X0)
% 0.33/0.54           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.33/0.54           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.33/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.33/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.33/0.54           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.33/0.54           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.33/0.54           | (v2_struct_0 @ sk_D)
% 0.33/0.54           | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['34', '43'])).
% 0.33/0.54  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('48', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('49', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.33/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.33/0.54  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('51', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('52', plain,
% 0.33/0.54      ((![X0 : $i]:
% 0.33/0.54          ((v2_struct_0 @ sk_A)
% 0.33/0.54           | (v2_struct_0 @ sk_C)
% 0.33/0.54           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.33/0.54           | ~ (r2_hidden @ sk_F @ X0)
% 0.33/0.54           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.33/0.54           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.33/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.33/0.54           | (v2_struct_0 @ sk_D)
% 0.33/0.54           | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('demod', [status(thm)],
% 0.33/0.54                ['44', '45', '46', '47', '48', '49', '50', '51'])).
% 0.33/0.54  thf('53', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.33/0.54         | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.33/0.54         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.33/0.54         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_A)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['31', '52'])).
% 0.33/0.54  thf(d10_xboole_0, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.54  thf('54', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.33/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.54  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.33/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.33/0.54  thf('56', plain,
% 0.33/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.33/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.33/0.54      inference('demod', [status(thm)], ['25', '30'])).
% 0.33/0.54  thf(t16_tsep_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.54               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.33/0.54                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.33/0.54                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('57', plain,
% 0.33/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.33/0.54         (~ (m1_pre_topc @ X14 @ X15)
% 0.33/0.54          | ((X16) != (u1_struct_0 @ X14))
% 0.33/0.54          | ~ (v1_tsep_1 @ X14 @ X15)
% 0.33/0.54          | ~ (m1_pre_topc @ X14 @ X15)
% 0.33/0.54          | (v3_pre_topc @ X16 @ X15)
% 0.33/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.33/0.54          | ~ (l1_pre_topc @ X15)
% 0.33/0.54          | ~ (v2_pre_topc @ X15))),
% 0.33/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.33/0.54  thf('58', plain,
% 0.33/0.54      (![X14 : $i, X15 : $i]:
% 0.33/0.54         (~ (v2_pre_topc @ X15)
% 0.33/0.54          | ~ (l1_pre_topc @ X15)
% 0.33/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.33/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.33/0.54          | (v3_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.33/0.54          | ~ (v1_tsep_1 @ X14 @ X15)
% 0.33/0.54          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.33/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.33/0.54  thf('59', plain,
% 0.33/0.54      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.33/0.54        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.33/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.33/0.54        | ~ (l1_pre_topc @ sk_D)
% 0.33/0.54        | ~ (v2_pre_topc @ sk_D))),
% 0.33/0.54      inference('sup-', [status(thm)], ['56', '58'])).
% 0.33/0.54  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('61', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('62', plain, ((l1_pre_topc @ sk_D)),
% 0.33/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.33/0.54  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(cc1_pre_topc, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.33/0.54  thf('64', plain,
% 0.33/0.54      (![X8 : $i, X9 : $i]:
% 0.33/0.54         (~ (m1_pre_topc @ X8 @ X9)
% 0.33/0.54          | (v2_pre_topc @ X8)
% 0.33/0.54          | ~ (l1_pre_topc @ X9)
% 0.33/0.54          | ~ (v2_pre_topc @ X9))),
% 0.33/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.33/0.54  thf('65', plain,
% 0.33/0.54      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.33/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.33/0.54  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('68', plain, ((v2_pre_topc @ sk_D)),
% 0.33/0.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.33/0.54  thf('69', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.33/0.54      inference('demod', [status(thm)], ['59', '60', '61', '62', '68'])).
% 0.33/0.54  thf('70', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.33/0.54         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_A)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('demod', [status(thm)], ['53', '55', '69'])).
% 0.33/0.54  thf('71', plain,
% 0.33/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.33/0.54         | (v2_struct_0 @ sk_A)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['22', '70'])).
% 0.33/0.54  thf('72', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.33/0.54      inference('split', [status(esa)], ['13'])).
% 0.33/0.54  thf('73', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_A)
% 0.33/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_C))))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.33/0.54  thf(fc2_struct_0, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.33/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.33/0.54  thf('74', plain,
% 0.33/0.54      (![X13 : $i]:
% 0.33/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.33/0.54          | ~ (l1_struct_0 @ X13)
% 0.33/0.54          | (v2_struct_0 @ X13))),
% 0.33/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.33/0.54  thf('75', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_A)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | ~ (l1_struct_0 @ sk_C)))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.33/0.54  thf('76', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('77', plain,
% 0.33/0.54      (![X11 : $i, X12 : $i]:
% 0.33/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.33/0.54          | (l1_pre_topc @ X11)
% 0.33/0.54          | ~ (l1_pre_topc @ X12))),
% 0.33/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.33/0.54  thf('78', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.33/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.33/0.54  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.33/0.54      inference('demod', [status(thm)], ['78', '79'])).
% 0.33/0.54  thf(dt_l1_pre_topc, axiom,
% 0.33/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.33/0.54  thf('81', plain,
% 0.33/0.54      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.33/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.33/0.54  thf('82', plain, ((l1_struct_0 @ sk_C)),
% 0.33/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.33/0.54  thf('83', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_A)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_C)))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('demod', [status(thm)], ['75', '82'])).
% 0.33/0.54  thf('84', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (v2_struct_0 @ sk_C)
% 0.33/0.54         | (v2_struct_0 @ sk_A)))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('simplify', [status(thm)], ['83'])).
% 0.33/0.54  thf('85', plain, (~ (v2_struct_0 @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('86', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.33/0.54  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('88', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('clc', [status(thm)], ['86', '87'])).
% 0.33/0.54  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('90', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_C))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.33/0.54      inference('clc', [status(thm)], ['88', '89'])).
% 0.33/0.54  thf('91', plain, (~ (v2_struct_0 @ sk_C)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('92', plain,
% 0.33/0.54      (~
% 0.33/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.33/0.54  thf('93', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.33/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.33/0.54      inference('split', [status(esa)], ['11'])).
% 0.33/0.54  thf('94', plain, (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.33/0.54      inference('sat_resolution*', [status(thm)], ['17', '21', '92', '93'])).
% 0.33/0.54  thf('95', plain, ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.33/0.54      inference('simpl_trail', [status(thm)], ['8', '94'])).
% 0.33/0.54  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.33/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.33/0.54  thf('97', plain,
% 0.33/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.33/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.33/0.54      inference('demod', [status(thm)], ['25', '30'])).
% 0.33/0.54  thf('98', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('99', plain,
% 0.33/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 0.33/0.54         X29 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X22)
% 0.33/0.54          | ~ (v2_pre_topc @ X22)
% 0.33/0.54          | ~ (l1_pre_topc @ X22)
% 0.33/0.54          | (v2_struct_0 @ X23)
% 0.33/0.54          | ~ (m1_pre_topc @ X23 @ X24)
% 0.33/0.54          | ~ (m1_pre_topc @ X25 @ X23)
% 0.37/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.37/0.54          | ~ (r1_tmap_1 @ X23 @ X22 @ X28 @ X29)
% 0.37/0.54          | (r1_tmap_1 @ X25 @ X22 @ 
% 0.37/0.54             (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.37/0.54          | ((X29) != (X27))
% 0.37/0.54          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.54          | ~ (r2_hidden @ X29 @ X26)
% 0.37/0.54          | ~ (v3_pre_topc @ X26 @ X23)
% 0.37/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X23))
% 0.37/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.54               (k1_zfmisc_1 @ 
% 0.37/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.37/0.54          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.37/0.54          | ~ (v1_funct_1 @ X28)
% 0.37/0.54          | ~ (m1_pre_topc @ X25 @ X24)
% 0.37/0.54          | (v2_struct_0 @ X25)
% 0.37/0.54          | ~ (l1_pre_topc @ X24)
% 0.37/0.54          | ~ (v2_pre_topc @ X24)
% 0.37/0.54          | (v2_struct_0 @ X24))),
% 0.37/0.54      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.37/0.54  thf('100', plain,
% 0.37/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.54         ((v2_struct_0 @ X24)
% 0.37/0.54          | ~ (v2_pre_topc @ X24)
% 0.37/0.54          | ~ (l1_pre_topc @ X24)
% 0.37/0.54          | (v2_struct_0 @ X25)
% 0.37/0.54          | ~ (m1_pre_topc @ X25 @ X24)
% 0.37/0.54          | ~ (v1_funct_1 @ X28)
% 0.37/0.54          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.37/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.54               (k1_zfmisc_1 @ 
% 0.37/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.37/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.37/0.54          | ~ (v3_pre_topc @ X26 @ X23)
% 0.37/0.54          | ~ (r2_hidden @ X27 @ X26)
% 0.37/0.54          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X25))
% 0.37/0.54          | (r1_tmap_1 @ X25 @ X22 @ 
% 0.37/0.54             (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ X28) @ X27)
% 0.37/0.54          | ~ (r1_tmap_1 @ X23 @ X22 @ X28 @ X27)
% 0.37/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.37/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.54          | ~ (m1_pre_topc @ X25 @ X23)
% 0.37/0.54          | ~ (m1_pre_topc @ X23 @ X24)
% 0.37/0.54          | (v2_struct_0 @ X23)
% 0.37/0.54          | ~ (l1_pre_topc @ X22)
% 0.37/0.54          | ~ (v2_pre_topc @ X22)
% 0.37/0.54          | (v2_struct_0 @ X22))),
% 0.37/0.54      inference('simplify', [status(thm)], ['99'])).
% 0.37/0.54  thf('101', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_B)
% 0.37/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.37/0.54          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.37/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.54          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.37/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.54          | (v2_struct_0 @ X1)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['98', '100'])).
% 0.37/0.54  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('104', plain,
% 0.37/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('105', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('106', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_B)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.37/0.54          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.37/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.54          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.54          | (v2_struct_0 @ X1)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.37/0.54  thf('107', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((v2_struct_0 @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X1)
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.37/0.54          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X1))
% 0.37/0.54          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | (v2_struct_0 @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['97', '106'])).
% 0.37/0.54  thf('108', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.37/0.54      inference('demod', [status(thm)], ['59', '60', '61', '62', '68'])).
% 0.37/0.54  thf('109', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((v2_struct_0 @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X1)
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X1))
% 0.37/0.54          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.37/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | (v2_struct_0 @ sk_B))),
% 0.37/0.54      inference('demod', [status(thm)], ['107', '108'])).
% 0.37/0.54  thf('110', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_B)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.37/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.37/0.54          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ X1)
% 0.37/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_C)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['96', '109'])).
% 0.37/0.54  thf('111', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('112', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_B)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.37/0.54          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ X1)
% 0.37/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_C)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.37/0.54  thf('113', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_C)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.37/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.37/0.54          | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.37/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | (v2_struct_0 @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['95', '112'])).
% 0.37/0.54  thf('114', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('115', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('116', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_C)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.37/0.54          | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | (v2_struct_0 @ sk_B))),
% 0.37/0.54      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.37/0.54  thf('117', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.37/0.54          | (v2_struct_0 @ sk_B)
% 0.37/0.54          | (v2_struct_0 @ sk_D)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.54          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.37/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_C)
% 0.37/0.54          | ~ (l1_pre_topc @ X0)
% 0.37/0.54          | ~ (v2_pre_topc @ X0)
% 0.37/0.54          | (v2_struct_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '116'])).
% 0.37/0.54  thf('118', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.37/0.54        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_B)
% 0.37/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '117'])).
% 0.37/0.54  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('122', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_B)
% 0.37/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.37/0.54      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.37/0.54  thf('123', plain,
% 0.37/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.37/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('124', plain,
% 0.37/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.37/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.37/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.54  thf('125', plain,
% 0.37/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.37/0.54      inference('split', [status(esa)], ['20'])).
% 0.37/0.54  thf('126', plain,
% 0.37/0.54      (~
% 0.37/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.37/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.37/0.54      inference('sup-', [status(thm)], ['124', '125'])).
% 0.37/0.54  thf('127', plain,
% 0.37/0.54      (~
% 0.37/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['17', '21', '92', '126'])).
% 0.37/0.54  thf('128', plain,
% 0.37/0.54      (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.37/0.54          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['123', '127'])).
% 0.37/0.54  thf('129', plain,
% 0.37/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.37/0.54        | (v2_struct_0 @ sk_B)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['122', '128'])).
% 0.37/0.54  thf('130', plain,
% 0.37/0.54      (![X13 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.37/0.54          | ~ (l1_struct_0 @ X13)
% 0.37/0.54          | (v2_struct_0 @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.54  thf('131', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_B)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | ~ (l1_struct_0 @ sk_C))),
% 0.37/0.54      inference('sup-', [status(thm)], ['129', '130'])).
% 0.37/0.54  thf('132', plain, ((l1_struct_0 @ sk_C)),
% 0.37/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.54  thf('133', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_B)
% 0.37/0.54        | (v2_struct_0 @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['131', '132'])).
% 0.37/0.54  thf('134', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_B)
% 0.37/0.54        | (v2_struct_0 @ sk_D)
% 0.37/0.54        | (v2_struct_0 @ sk_C)
% 0.37/0.54        | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('simplify', [status(thm)], ['133'])).
% 0.37/0.54  thf('135', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('136', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['134', '135'])).
% 0.37/0.54  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('138', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.37/0.54      inference('clc', [status(thm)], ['136', '137'])).
% 0.37/0.54  thf('139', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('140', plain, ((v2_struct_0 @ sk_C)),
% 0.37/0.54      inference('clc', [status(thm)], ['138', '139'])).
% 0.37/0.54  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
