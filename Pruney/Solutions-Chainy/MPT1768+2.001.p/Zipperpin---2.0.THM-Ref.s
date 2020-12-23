%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MKNlX7QTtX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  240 (1586 expanded)
%              Number of leaves         :   44 ( 477 expanded)
%              Depth                    :   32
%              Number of atoms          : 3247 (58125 expanded)
%              Number of equality atoms :   60 ( 162 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t79_tmap_1,conjecture,(
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
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ D @ C )
                          & ( m1_pre_topc @ E @ D ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) )).

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
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ D @ C )
                            & ( m1_pre_topc @ E @ D ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( r1_tarski @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
        & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( zip_tseitin_1 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( zip_tseitin_0 @ X13 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_F @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_F @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v1_funct_2 @ ( k2_partfun1 @ X4 @ X5 @ X6 @ X7 ) @ X7 @ X5 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('31',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','29','30','31','32','33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','40'])).

thf('42',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X4 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','54','59','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('75',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ( m1_pre_topc @ X38 @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','40'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('94',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['72','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['73','79'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

thf('104',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X31 ) @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ ( k2_tmap_1 @ X33 @ X31 @ X35 @ X32 ) ) @ ( k2_tmap_1 @ X33 @ X31 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('107',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('108',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_E @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X0 @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','71'])).

thf('120',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['119','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','146'])).

thf('148',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('149',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['132','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['73','79'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','29','30','31','32','33','34'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['73','79'])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['155','171'])).

thf('173',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['118','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('178',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('179',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('180',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('181',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('182',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('183',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','183'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    $false ),
    inference(demod,[status(thm)],['0','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MKNlX7QTtX
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 283 iterations in 0.269s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.53/0.73  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.53/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.73  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.53/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.53/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.73  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.53/0.73  thf(t79_tmap_1, conjecture,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.73             ( l1_pre_topc @ B ) ) =>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.73               ( ![D:$i]:
% 0.53/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.73                   ( ![E:$i]:
% 0.53/0.73                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.53/0.73                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.53/0.73                         ( ![F:$i]:
% 0.53/0.73                           ( ( ( v1_funct_1 @ F ) & 
% 0.53/0.73                               ( v1_funct_2 @
% 0.53/0.73                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.73                               ( m1_subset_1 @
% 0.53/0.73                                 F @ 
% 0.53/0.73                                 ( k1_zfmisc_1 @
% 0.53/0.73                                   ( k2_zfmisc_1 @
% 0.53/0.73                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.73                             ( r2_funct_2 @
% 0.53/0.73                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.73                               ( k3_tmap_1 @
% 0.53/0.73                                 A @ B @ D @ E @ 
% 0.53/0.73                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.53/0.73                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i]:
% 0.53/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.53/0.73            ( l1_pre_topc @ A ) ) =>
% 0.53/0.73          ( ![B:$i]:
% 0.53/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.73                ( l1_pre_topc @ B ) ) =>
% 0.53/0.73              ( ![C:$i]:
% 0.53/0.73                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.73                  ( ![D:$i]:
% 0.53/0.73                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.73                      ( ![E:$i]:
% 0.53/0.73                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.53/0.73                          ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.53/0.73                            ( ![F:$i]:
% 0.53/0.73                              ( ( ( v1_funct_1 @ F ) & 
% 0.53/0.73                                  ( v1_funct_2 @
% 0.53/0.73                                    F @ ( u1_struct_0 @ C ) @ 
% 0.53/0.73                                    ( u1_struct_0 @ B ) ) & 
% 0.53/0.73                                  ( m1_subset_1 @
% 0.53/0.73                                    F @ 
% 0.53/0.73                                    ( k1_zfmisc_1 @
% 0.53/0.73                                      ( k2_zfmisc_1 @
% 0.53/0.73                                        ( u1_struct_0 @ C ) @ 
% 0.53/0.73                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.73                                ( r2_funct_2 @
% 0.53/0.73                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.73                                  ( k3_tmap_1 @
% 0.53/0.73                                    A @ B @ D @ E @ 
% 0.53/0.73                                    ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.53/0.73                                  ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t79_tmap_1])).
% 0.53/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t35_borsuk_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( l1_pre_topc @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.53/0.73           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X29 : $i, X30 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X29 @ X30)
% 0.53/0.73          | (r1_tarski @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 0.53/0.73          | ~ (l1_pre_topc @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      ((~ (l1_pre_topc @ sk_C)
% 0.53/0.73        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.73  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(dt_m1_pre_topc, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( l1_pre_topc @ A ) =>
% 0.53/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X17 @ X18)
% 0.53/0.73          | (l1_pre_topc @ X17)
% 0.53/0.73          | ~ (l1_pre_topc @ X18))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.53/0.73  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.73  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('9', plain, ((l1_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('10', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.53/0.73      inference('demod', [status(thm)], ['4', '9'])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_F @ 
% 0.53/0.73        (k1_zfmisc_1 @ 
% 0.53/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t38_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.53/0.73       ( ( r1_tarski @ C @ A ) =>
% 0.53/0.73         ( ( ( m1_subset_1 @
% 0.53/0.73               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.53/0.73               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.53/0.73             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.53/0.73             ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) ) | 
% 0.53/0.73           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.53/0.73  thf(zf_stmt_2, axiom,
% 0.53/0.73    (![B:$i,A:$i]:
% 0.53/0.73     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.53/0.73       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.53/0.73  thf(zf_stmt_4, axiom,
% 0.53/0.73    (![D:$i,C:$i,B:$i,A:$i]:
% 0.53/0.73     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.53/0.73       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.53/0.73         ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.53/0.73         ( m1_subset_1 @
% 0.53/0.73           ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.53/0.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_5, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ( r1_tarski @ C @ A ) =>
% 0.53/0.73         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ))).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X10 @ X11)
% 0.53/0.73          | (zip_tseitin_1 @ X12 @ X11)
% 0.53/0.73          | ~ (v1_funct_1 @ X13)
% 0.53/0.73          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.53/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.53/0.73          | (zip_tseitin_0 @ X13 @ X10 @ X12 @ X11))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_0 @ sk_F @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (u1_struct_0 @ sk_C))
% 0.53/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('15', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_0 @ sk_F @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (u1_struct_0 @ sk_C))
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (zip_tseitin_0 @ sk_F @ (u1_struct_0 @ sk_D) @ 
% 0.53/0.73           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['10', '16'])).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.73         ((v1_funct_2 @ (k2_partfun1 @ X4 @ X5 @ X6 @ X7) @ X7 @ X5)
% 0.53/0.73          | ~ (zip_tseitin_0 @ X6 @ X7 @ X5 @ X4))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v1_funct_2 @ 
% 0.53/0.73           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)) @ 
% 0.53/0.73           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.73  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_F @ 
% 0.53/0.73        (k1_zfmisc_1 @ 
% 0.53/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(d4_tmap_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.73             ( l1_pre_topc @ B ) ) =>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.73                 ( m1_subset_1 @
% 0.53/0.73                   C @ 
% 0.53/0.73                   ( k1_zfmisc_1 @
% 0.53/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.73               ( ![D:$i]:
% 0.53/0.73                 ( ( m1_pre_topc @ D @ A ) =>
% 0.53/0.73                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.53/0.73                     ( k2_partfun1 @
% 0.53/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.53/0.73                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X20)
% 0.53/0.73          | ~ (v2_pre_topc @ X20)
% 0.53/0.73          | ~ (l1_pre_topc @ X20)
% 0.53/0.73          | ~ (m1_pre_topc @ X21 @ X22)
% 0.53/0.73          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.53/0.73                 X23 @ (u1_struct_0 @ X21)))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ 
% 0.53/0.73               (k1_zfmisc_1 @ 
% 0.53/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.53/0.73          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.53/0.73          | ~ (v1_funct_1 @ X23)
% 0.53/0.73          | ~ (l1_pre_topc @ X22)
% 0.53/0.73          | ~ (v2_pre_topc @ X22)
% 0.53/0.73          | (v2_struct_0 @ X22))),
% 0.53/0.73      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_C)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_C)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_C)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.53/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.73  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc1_pre_topc, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      (![X14 : $i, X15 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X14 @ X15)
% 0.53/0.73          | (v2_pre_topc @ X14)
% 0.53/0.73          | ~ (l1_pre_topc @ X15)
% 0.53/0.73          | ~ (v2_pre_topc @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.53/0.73  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('29', plain, ((v2_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.53/0.73  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('31', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('34', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('35', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_C)
% 0.53/0.73          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)],
% 0.53/0.73                ['23', '29', '30', '31', '32', '33', '34'])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_D)))
% 0.53/0.73        | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['20', '35'])).
% 0.53/0.73  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('38', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.53/0.73      inference('clc', [status(thm)], ['36', '37'])).
% 0.53/0.73  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('40', plain,
% 0.53/0.73      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['19', '40'])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (zip_tseitin_0 @ sk_F @ (u1_struct_0 @ sk_D) @ 
% 0.53/0.73           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['10', '16'])).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.73         ((m1_subset_1 @ (k2_partfun1 @ X4 @ X5 @ X6 @ X7) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.53/0.73          | ~ (zip_tseitin_0 @ X6 @ X7 @ X5 @ X4))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (m1_subset_1 @ 
% 0.53/0.73           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)) @ 
% 0.53/0.73           (k1_zfmisc_1 @ 
% 0.53/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.73  thf('45', plain,
% 0.53/0.73      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.53/0.73  thf('46', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73           (k1_zfmisc_1 @ 
% 0.53/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['44', '45'])).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X20)
% 0.53/0.73          | ~ (v2_pre_topc @ X20)
% 0.53/0.73          | ~ (l1_pre_topc @ X20)
% 0.53/0.73          | ~ (m1_pre_topc @ X21 @ X22)
% 0.53/0.73          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.53/0.73                 X23 @ (u1_struct_0 @ X21)))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ 
% 0.53/0.73               (k1_zfmisc_1 @ 
% 0.53/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.53/0.73          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.53/0.73          | ~ (v1_funct_1 @ X23)
% 0.53/0.73          | ~ (l1_pre_topc @ X22)
% 0.53/0.73          | ~ (v2_pre_topc @ X22)
% 0.53/0.73          | (v2_struct_0 @ X22))),
% 0.53/0.73      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_D)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_D)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_D)
% 0.53/0.73          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.53/0.73  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      (![X14 : $i, X15 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X14 @ X15)
% 0.53/0.73          | (v2_pre_topc @ X14)
% 0.53/0.73          | ~ (l1_pre_topc @ X15)
% 0.53/0.73          | ~ (v2_pre_topc @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.73  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('54', plain, ((v2_pre_topc @ sk_D)),
% 0.53/0.73      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.53/0.73  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X17 @ X18)
% 0.53/0.73          | (l1_pre_topc @ X17)
% 0.53/0.73          | ~ (l1_pre_topc @ X18))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.53/0.73  thf('57', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['55', '56'])).
% 0.53/0.73  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 0.53/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.53/0.73  thf('61', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_F @ 
% 0.53/0.73        (k1_zfmisc_1 @ 
% 0.53/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(dt_k2_partfun1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.53/0.73         ( m1_subset_1 @
% 0.53/0.73           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.53/0.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.53/0.73  thf('62', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.53/0.73          | ~ (v1_funct_1 @ X0)
% 0.53/0.73          | (v1_funct_1 @ (k2_partfun1 @ X1 @ X2 @ X0 @ X3)))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v1_funct_1 @ 
% 0.53/0.73           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            X0))
% 0.53/0.73          | ~ (v1_funct_1 @ sk_F))),
% 0.53/0.73      inference('sup-', [status(thm)], ['61', '62'])).
% 0.53/0.73  thf('64', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (v1_funct_1 @ 
% 0.53/0.73          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73           X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['63', '64'])).
% 0.53/0.73  thf('66', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.53/0.73      inference('sup+', [status(thm)], ['60', '65'])).
% 0.53/0.73  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('68', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_D)
% 0.53/0.73          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['48', '54', '59', '66', '67', '68'])).
% 0.53/0.73  thf('70', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | (v2_struct_0 @ sk_D)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['41', '69'])).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_D)
% 0.53/0.73          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['70'])).
% 0.53/0.73  thf('72', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | (v2_struct_0 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['1', '71'])).
% 0.53/0.73  thf('73', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t7_tsep_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.53/0.73           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.53/0.73  thf('75', plain,
% 0.53/0.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.53/0.73         (~ (m1_pre_topc @ X36 @ X37)
% 0.53/0.73          | (m1_pre_topc @ X38 @ X37)
% 0.53/0.73          | ~ (m1_pre_topc @ X38 @ X36)
% 0.53/0.73          | ~ (l1_pre_topc @ X37)
% 0.53/0.73          | ~ (v2_pre_topc @ X37))),
% 0.53/0.73      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.53/0.73  thf('76', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v2_pre_topc @ sk_C)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | (m1_pre_topc @ X0 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.53/0.73  thf('77', plain, ((v2_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.53/0.73  thf('78', plain, ((l1_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('79', plain,
% 0.53/0.73      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.53/0.73      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.53/0.73  thf('80', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '79'])).
% 0.53/0.73  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('82', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['19', '40'])).
% 0.53/0.73  thf('83', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73           (k1_zfmisc_1 @ 
% 0.53/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['44', '45'])).
% 0.53/0.73  thf(d5_tmap_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.73             ( l1_pre_topc @ B ) ) =>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( m1_pre_topc @ C @ A ) =>
% 0.53/0.73               ( ![D:$i]:
% 0.53/0.73                 ( ( m1_pre_topc @ D @ A ) =>
% 0.53/0.73                   ( ![E:$i]:
% 0.53/0.73                     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.73                         ( v1_funct_2 @
% 0.53/0.73                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.73                         ( m1_subset_1 @
% 0.53/0.73                           E @ 
% 0.53/0.73                           ( k1_zfmisc_1 @
% 0.53/0.73                             ( k2_zfmisc_1 @
% 0.53/0.73                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.73                       ( ( m1_pre_topc @ D @ C ) =>
% 0.53/0.73                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.53/0.73                           ( k2_partfun1 @
% 0.53/0.73                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.53/0.73                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf('84', plain,
% 0.53/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X24)
% 0.53/0.73          | ~ (v2_pre_topc @ X24)
% 0.53/0.73          | ~ (l1_pre_topc @ X24)
% 0.53/0.73          | ~ (m1_pre_topc @ X25 @ X26)
% 0.53/0.73          | ~ (m1_pre_topc @ X25 @ X27)
% 0.53/0.73          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.53/0.73                 X28 @ (u1_struct_0 @ X25)))
% 0.53/0.73          | ~ (m1_subset_1 @ X28 @ 
% 0.53/0.73               (k1_zfmisc_1 @ 
% 0.53/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.53/0.73          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.53/0.73          | ~ (v1_funct_1 @ X28)
% 0.53/0.73          | ~ (m1_pre_topc @ X27 @ X26)
% 0.53/0.73          | ~ (l1_pre_topc @ X26)
% 0.53/0.73          | ~ (v2_pre_topc @ X26)
% 0.53/0.73          | (v2_struct_0 @ X26))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.53/0.73  thf('85', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.53/0.73          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['83', '84'])).
% 0.53/0.73  thf('86', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.53/0.73      inference('sup+', [status(thm)], ['60', '65'])).
% 0.53/0.73  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('89', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.53/0.73  thf('90', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['82', '89'])).
% 0.53/0.73  thf('91', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['90'])).
% 0.53/0.73  thf('92', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (l1_pre_topc @ sk_C)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['81', '91'])).
% 0.53/0.73  thf('93', plain, ((l1_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('94', plain, ((v2_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.53/0.73  thf('95', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.53/0.73  thf('96', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['80', '95'])).
% 0.53/0.73  thf('97', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('98', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('demod', [status(thm)], ['96', '97'])).
% 0.53/0.73  thf('99', plain,
% 0.53/0.73      ((((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73          = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup+', [status(thm)], ['72', '98'])).
% 0.53/0.73  thf('100', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['99'])).
% 0.53/0.73  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('102', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '79'])).
% 0.53/0.73  thf('103', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_F @ 
% 0.53/0.73        (k1_zfmisc_1 @ 
% 0.53/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t78_tmap_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.73             ( l1_pre_topc @ B ) ) =>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.73               ( ![D:$i]:
% 0.53/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.73                   ( ![E:$i]:
% 0.53/0.73                     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.73                         ( v1_funct_2 @
% 0.53/0.73                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.73                         ( m1_subset_1 @
% 0.53/0.73                           E @ 
% 0.53/0.73                           ( k1_zfmisc_1 @
% 0.53/0.73                             ( k2_zfmisc_1 @
% 0.53/0.73                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.73                       ( ( m1_pre_topc @ C @ D ) =>
% 0.53/0.73                         ( r2_funct_2 @
% 0.53/0.73                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.73                           ( k3_tmap_1 @
% 0.53/0.73                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.53/0.73                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf('104', plain,
% 0.53/0.73      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X31)
% 0.53/0.73          | ~ (v2_pre_topc @ X31)
% 0.53/0.73          | ~ (l1_pre_topc @ X31)
% 0.53/0.73          | (v2_struct_0 @ X32)
% 0.53/0.73          | ~ (m1_pre_topc @ X32 @ X33)
% 0.53/0.73          | ~ (m1_pre_topc @ X34 @ X32)
% 0.53/0.73          | (r2_funct_2 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X31) @ 
% 0.53/0.73             (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ 
% 0.53/0.73              (k2_tmap_1 @ X33 @ X31 @ X35 @ X32)) @ 
% 0.53/0.73             (k2_tmap_1 @ X33 @ X31 @ X35 @ X34))
% 0.53/0.73          | ~ (m1_subset_1 @ X35 @ 
% 0.53/0.73               (k1_zfmisc_1 @ 
% 0.53/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 0.53/0.73          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 0.53/0.73          | ~ (v1_funct_1 @ X35)
% 0.53/0.73          | ~ (m1_pre_topc @ X34 @ X33)
% 0.53/0.73          | (v2_struct_0 @ X34)
% 0.53/0.73          | ~ (l1_pre_topc @ X33)
% 0.53/0.73          | ~ (v2_pre_topc @ X33)
% 0.53/0.73          | (v2_struct_0 @ X33))),
% 0.53/0.73      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.53/0.73  thf('105', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_C)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_C)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.53/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.53/0.73             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ X1)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ X1)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['103', '104'])).
% 0.53/0.73  thf('106', plain, ((v2_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.53/0.73  thf('107', plain, ((l1_pre_topc @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('108', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('109', plain,
% 0.53/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('111', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('112', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.53/0.73             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ X1)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ X1)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)],
% 0.53/0.73                ['105', '106', '107', '108', '109', '110', '111'])).
% 0.53/0.73  thf('113', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_E @ X0)
% 0.53/0.73          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73             (k3_tmap_1 @ sk_C @ sk_B @ X0 @ sk_E @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)) @ 
% 0.53/0.73             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73          | (v2_struct_0 @ sk_E)
% 0.53/0.73          | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['102', '112'])).
% 0.53/0.73  thf('114', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['101', '113'])).
% 0.53/0.73  thf('115', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('116', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['114', '115'])).
% 0.53/0.73  thf('117', plain,
% 0.53/0.73      (((r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73         (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.53/0.73          sk_E) @ 
% 0.53/0.73         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup+', [status(thm)], ['100', '116'])).
% 0.53/0.73  thf('118', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['117'])).
% 0.53/0.73  thf('119', plain,
% 0.53/0.73      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | (v2_struct_0 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['1', '71'])).
% 0.53/0.73  thf('120', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('121', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('122', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['90'])).
% 0.53/0.73  thf('123', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.73          | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['121', '122'])).
% 0.53/0.73  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('126', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73          | (v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.73          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.73              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.53/0.73          | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.53/0.73  thf('127', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['120', '126'])).
% 0.53/0.73  thf('128', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('129', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.53/0.73      inference('demod', [status(thm)], ['127', '128'])).
% 0.53/0.73  thf('130', plain,
% 0.53/0.73      ((((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73          = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup+', [status(thm)], ['119', '129'])).
% 0.53/0.73  thf('131', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['130'])).
% 0.53/0.73  thf('132', plain,
% 0.53/0.73      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)) @ 
% 0.53/0.73          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('134', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('135', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_F @ 
% 0.53/0.73        (k1_zfmisc_1 @ 
% 0.53/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('136', plain,
% 0.53/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X24)
% 0.53/0.73          | ~ (v2_pre_topc @ X24)
% 0.53/0.73          | ~ (l1_pre_topc @ X24)
% 0.53/0.73          | ~ (m1_pre_topc @ X25 @ X26)
% 0.53/0.73          | ~ (m1_pre_topc @ X25 @ X27)
% 0.53/0.73          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.53/0.73                 X28 @ (u1_struct_0 @ X25)))
% 0.53/0.73          | ~ (m1_subset_1 @ X28 @ 
% 0.53/0.73               (k1_zfmisc_1 @ 
% 0.53/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.53/0.73          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.53/0.73          | ~ (v1_funct_1 @ X28)
% 0.53/0.73          | ~ (m1_pre_topc @ X27 @ X26)
% 0.53/0.73          | ~ (l1_pre_topc @ X26)
% 0.53/0.73          | ~ (v2_pre_topc @ X26)
% 0.53/0.73          | (v2_struct_0 @ X26))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.53/0.73  thf('137', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.53/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['135', '136'])).
% 0.53/0.73  thf('138', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('139', plain,
% 0.53/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('140', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('141', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('142', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v2_struct_0 @ X0)
% 0.53/0.73          | ~ (v2_pre_topc @ X0)
% 0.53/0.73          | ~ (l1_pre_topc @ X0)
% 0.53/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.53/0.73          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X1)))
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.53/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.53/0.73  thf('143', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.73          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.73          | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['134', '142'])).
% 0.53/0.73  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('146', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.53/0.73  thf('147', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_D)))
% 0.53/0.73        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['133', '146'])).
% 0.53/0.73  thf('148', plain,
% 0.53/0.73      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.53/0.73         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.53/0.73  thf('149', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('150', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.73            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.53/0.73  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('152', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.73            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['150', '151'])).
% 0.53/0.73  thf('153', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('154', plain,
% 0.53/0.73      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.53/0.73         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.53/0.73      inference('clc', [status(thm)], ['152', '153'])).
% 0.53/0.73  thf('155', plain,
% 0.53/0.73      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.53/0.73          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.53/0.73      inference('demod', [status(thm)], ['132', '154'])).
% 0.53/0.73  thf('156', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('157', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_B)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.53/0.73  thf('158', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['156', '157'])).
% 0.53/0.73  thf('159', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '79'])).
% 0.53/0.73  thf('160', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((v2_struct_0 @ sk_C)
% 0.53/0.73          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.53/0.73              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73                 sk_F @ (u1_struct_0 @ X0)))
% 0.53/0.73          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.53/0.73          | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)],
% 0.53/0.73                ['23', '29', '30', '31', '32', '33', '34'])).
% 0.53/0.73  thf('161', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_E)))
% 0.53/0.73        | (v2_struct_0 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['159', '160'])).
% 0.53/0.73  thf('162', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('163', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_C)
% 0.53/0.73        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.53/0.73            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.53/0.73      inference('clc', [status(thm)], ['161', '162'])).
% 0.53/0.73  thf('164', plain, (~ (v2_struct_0 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('165', plain,
% 0.53/0.73      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.53/0.73         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.53/0.73            (u1_struct_0 @ sk_E)))),
% 0.53/0.73      inference('clc', [status(thm)], ['163', '164'])).
% 0.53/0.73  thf('166', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '79'])).
% 0.53/0.73  thf('167', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.53/0.73            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['158', '165', '166'])).
% 0.53/0.73  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('169', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_B)
% 0.53/0.73        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.53/0.73            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.53/0.73      inference('clc', [status(thm)], ['167', '168'])).
% 0.53/0.73  thf('170', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('171', plain,
% 0.53/0.73      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.53/0.73         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.53/0.73      inference('clc', [status(thm)], ['169', '170'])).
% 0.53/0.73  thf('172', plain,
% 0.53/0.73      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.53/0.73          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.53/0.73      inference('demod', [status(thm)], ['155', '171'])).
% 0.53/0.73  thf('173', plain,
% 0.53/0.73      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.53/0.73            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.53/0.73           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['131', '172'])).
% 0.53/0.73  thf('174', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_A)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['118', '173'])).
% 0.53/0.73  thf('175', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D))),
% 0.53/0.73      inference('simplify', [status(thm)], ['174'])).
% 0.53/0.73  thf('176', plain,
% 0.53/0.73      (![X8 : $i, X9 : $i]:
% 0.53/0.73         (((X8) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X8 @ X9))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.73  thf('177', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_A)
% 0.53/0.73        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['175', '176'])).
% 0.53/0.73  thf(fc2_struct_0, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.73       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.73  thf('178', plain,
% 0.53/0.73      (![X19 : $i]:
% 0.53/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.53/0.73          | ~ (l1_struct_0 @ X19)
% 0.53/0.73          | (v2_struct_0 @ X19))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.53/0.73  thf('179', plain,
% 0.53/0.73      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.73        | (v2_struct_0 @ sk_A)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.73        | (v2_struct_0 @ sk_C)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | (v2_struct_0 @ sk_D)
% 0.53/0.73        | (v2_struct_0 @ sk_B)
% 0.53/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['177', '178'])).
% 0.53/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.73  thf('180', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.73  thf('181', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(dt_l1_pre_topc, axiom,
% 0.53/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.53/0.73  thf('182', plain,
% 0.53/0.73      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.73  thf('183', plain, ((l1_struct_0 @ sk_B)),
% 0.53/0.73      inference('sup-', [status(thm)], ['181', '182'])).
% 0.53/0.73  thf('184', plain,
% 0.53/0.73      (((v2_struct_0 @ sk_A)
% 0.53/0.73        | (v2_struct_0 @ sk_E)
% 0.53/0.74        | (v2_struct_0 @ sk_C)
% 0.53/0.74        | (v2_struct_0 @ sk_B)
% 0.53/0.74        | (v2_struct_0 @ sk_D)
% 0.53/0.74        | (v2_struct_0 @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['179', '180', '183'])).
% 0.53/0.74  thf('185', plain,
% 0.53/0.74      (((v2_struct_0 @ sk_D)
% 0.53/0.74        | (v2_struct_0 @ sk_B)
% 0.53/0.74        | (v2_struct_0 @ sk_C)
% 0.53/0.74        | (v2_struct_0 @ sk_E)
% 0.53/0.74        | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('simplify', [status(thm)], ['184'])).
% 0.53/0.74  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('187', plain,
% 0.53/0.74      (((v2_struct_0 @ sk_A)
% 0.53/0.74        | (v2_struct_0 @ sk_E)
% 0.53/0.74        | (v2_struct_0 @ sk_C)
% 0.53/0.74        | (v2_struct_0 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['185', '186'])).
% 0.53/0.74  thf('188', plain, (~ (v2_struct_0 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('189', plain,
% 0.53/0.74      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['187', '188'])).
% 0.53/0.74  thf('190', plain, (~ (v2_struct_0 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('191', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E))),
% 0.53/0.74      inference('clc', [status(thm)], ['189', '190'])).
% 0.53/0.74  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('193', plain, ((v2_struct_0 @ sk_E)),
% 0.53/0.74      inference('clc', [status(thm)], ['191', '192'])).
% 0.53/0.74  thf('194', plain, ($false), inference('demod', [status(thm)], ['0', '193'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
