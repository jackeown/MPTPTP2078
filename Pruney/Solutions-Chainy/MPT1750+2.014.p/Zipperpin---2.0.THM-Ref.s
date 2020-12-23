%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LIivawSVvC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  144 (1229 expanded)
%              Number of leaves         :   40 ( 379 expanded)
%              Depth                    :   28
%              Number of atoms          : 1330 (29846 expanded)
%              Number of equality atoms :   55 ( 641 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t60_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( v1_partfun1 @ X7 @ X8 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_partfun1 @ X11 @ X10 )
      | ( ( k1_relat_1 @ X11 )
        = X10 )
      | ~ ( v4_relat_1 @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r1_funct_2 @ X25 @ X26 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('40',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('42',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('49',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( g1_pre_topc @ X23 @ X24 )
       != ( g1_pre_topc @ X21 @ X22 ) )
      | ( X24 = X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('58',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( g1_pre_topc @ X23 @ X24 )
       != ( g1_pre_topc @ X21 @ X22 ) )
      | ( X23 = X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = X0 )
      | ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( k2_tmap_1 @ X33 @ X31 @ X34 @ X32 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) @ X34 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k2_partfun1 @ X13 @ X14 @ X12 @ X15 )
        = ( k7_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['64','92'])).

thf('94',plain,
    ( ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('96',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','96'])).

thf('98',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('101',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LIivawSVvC
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:35:10 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 83 iterations in 0.041s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.23/0.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.53  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.23/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.53  thf(t60_tmap_1, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53             ( l1_pre_topc @ B ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.23/0.53               ( ![D:$i]:
% 0.23/0.53                 ( ( ( v1_funct_1 @ D ) & 
% 0.23/0.53                     ( v1_funct_2 @
% 0.23/0.53                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.23/0.53                     ( m1_subset_1 @
% 0.23/0.53                       D @ 
% 0.23/0.53                       ( k1_zfmisc_1 @
% 0.23/0.53                         ( k2_zfmisc_1 @
% 0.23/0.53                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.23/0.53                   ( ( ( g1_pre_topc @
% 0.23/0.53                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.23/0.53                       ( g1_pre_topc @
% 0.23/0.53                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.23/0.53                     ( r1_funct_2 @
% 0.23/0.53                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.23/0.53                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.23/0.53                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.53            ( l1_pre_topc @ A ) ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53                ( l1_pre_topc @ B ) ) =>
% 0.23/0.53              ( ![C:$i]:
% 0.23/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.23/0.53                  ( ![D:$i]:
% 0.23/0.53                    ( ( ( v1_funct_1 @ D ) & 
% 0.23/0.53                        ( v1_funct_2 @
% 0.23/0.53                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.23/0.53                        ( m1_subset_1 @
% 0.23/0.53                          D @ 
% 0.23/0.53                          ( k1_zfmisc_1 @
% 0.23/0.53                            ( k2_zfmisc_1 @
% 0.23/0.53                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.23/0.53                      ( ( ( g1_pre_topc @
% 0.23/0.53                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.23/0.53                          ( g1_pre_topc @
% 0.23/0.53                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.23/0.53                        ( r1_funct_2 @
% 0.23/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.23/0.53                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.23/0.53                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.23/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc5_funct_2, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.53       ( ![C:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.23/0.53             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.23/0.53          | (v1_partfun1 @ X7 @ X8)
% 0.23/0.53          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.23/0.53          | ~ (v1_funct_1 @ X7)
% 0.23/0.53          | (v1_xboole_0 @ X9))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.53  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.23/0.53  thf(d4_partfun1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.23/0.53       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i]:
% 0.23/0.53         (~ (v1_partfun1 @ X11 @ X10)
% 0.23/0.53          | ((k1_relat_1 @ X11) = (X10))
% 0.23/0.53          | ~ (v4_relat_1 @ X11 @ X10)
% 0.23/0.53          | ~ (v1_relat_1 @ X11))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.23/0.53  thf('9', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.23/0.53        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.23/0.53        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc1_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( v1_relat_1 @ C ) ))).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         ((v1_relat_1 @ X1)
% 0.23/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.53  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc2_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.53         ((v4_relat_1 @ X4 @ X5)
% 0.23/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.53  thf('15', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.23/0.53  thf(fc2_struct_0, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      (![X20 : $i]:
% 0.23/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.23/0.53          | ~ (l1_struct_0 @ X20)
% 0.23/0.53          | (v2_struct_0 @ X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.23/0.53        | (v2_struct_0 @ sk_A)
% 0.23/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.53  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_l1_pre_topc, axiom,
% 0.23/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.53  thf('20', plain,
% 0.23/0.53      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.53  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.23/0.53  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('24', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('25', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '24'])).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '24'])).
% 0.23/0.53  thf(reflexivity_r1_funct_2, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.53     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.23/0.53         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.23/0.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.23/0.53         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.23/0.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.23/0.53       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.23/0.53         ((r1_funct_2 @ X25 @ X26 @ X27 @ X28 @ X29 @ X29)
% 0.23/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.23/0.53          | ~ (v1_funct_2 @ X29 @ X25 @ X26)
% 0.23/0.53          | ~ (v1_funct_1 @ X29)
% 0.23/0.53          | (v1_xboole_0 @ X28)
% 0.23/0.53          | (v1_xboole_0 @ X26)
% 0.23/0.53          | ~ (v1_funct_1 @ X30)
% 0.23/0.53          | ~ (v1_funct_2 @ X30 @ X27 @ X28)
% 0.23/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.23/0.53      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.23/0.53          | ~ (v1_funct_1 @ X2)
% 0.23/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v1_xboole_0 @ X0)
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.23/0.53             X0 @ sk_D @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.53  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('31', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('33', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.23/0.53          | ~ (v1_funct_1 @ X2)
% 0.23/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v1_xboole_0 @ X0)
% 0.23/0.53          | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.23/0.53             X0 @ sk_D @ sk_D))),
% 0.23/0.53      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.23/0.53  thf('34', plain,
% 0.23/0.53      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['25', '33'])).
% 0.23/0.53  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.23/0.53  thf('38', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.23/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.23/0.53  thf(t98_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) =>
% 0.23/0.53       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.53  thf('39', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.23/0.53  thf('40', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('41', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.23/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('44', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.23/0.53  thf('47', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf(dt_u1_pre_topc, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( m1_subset_1 @
% 0.23/0.53         ( u1_pre_topc @ A ) @ 
% 0.23/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      (![X19 : $i]:
% 0.23/0.53         ((m1_subset_1 @ (u1_pre_topc @ X19) @ 
% 0.23/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.23/0.53          | ~ (l1_pre_topc @ X19))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.23/0.53  thf('49', plain,
% 0.23/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.23/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))
% 0.23/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.23/0.53      inference('sup+', [status(thm)], ['47', '48'])).
% 0.23/0.53  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('51', plain,
% 0.23/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.23/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.23/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.53  thf(free_g1_pre_topc, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.53       ( ![C:$i,D:$i]:
% 0.23/0.53         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.23/0.53           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.23/0.53  thf('52', plain,
% 0.23/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.23/0.53         (((g1_pre_topc @ X23 @ X24) != (g1_pre_topc @ X21 @ X22))
% 0.23/0.53          | ((X24) = (X22))
% 0.23/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.23/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.23/0.53  thf('53', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((u1_pre_topc @ sk_B) = (X0))
% 0.23/0.53          | ((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.23/0.53              != (g1_pre_topc @ X1 @ X0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.53  thf('54', plain,
% 0.23/0.53      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.23/0.53          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.23/0.53        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['46', '53'])).
% 0.23/0.53  thf('55', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.23/0.53      inference('simplify', [status(thm)], ['54'])).
% 0.23/0.53  thf('56', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))),
% 0.23/0.53      inference('demod', [status(thm)], ['45', '55'])).
% 0.23/0.53  thf('57', plain,
% 0.23/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.23/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.23/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.53  thf('58', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.23/0.53      inference('simplify', [status(thm)], ['54'])).
% 0.23/0.53  thf('59', plain,
% 0.23/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.23/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.23/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.53  thf('60', plain,
% 0.23/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.23/0.53         (((g1_pre_topc @ X23 @ X24) != (g1_pre_topc @ X21 @ X22))
% 0.23/0.53          | ((X23) = (X21))
% 0.23/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.23/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.23/0.53  thf('61', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((k1_relat_1 @ sk_D) = (X0))
% 0.23/0.53          | ((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.23/0.53              != (g1_pre_topc @ X0 @ X1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.23/0.53  thf('62', plain,
% 0.23/0.53      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.23/0.53          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))
% 0.23/0.53        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['56', '61'])).
% 0.23/0.53  thf('63', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('simplify', [status(thm)], ['62'])).
% 0.23/0.53  thf('64', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.23/0.53      inference('demod', [status(thm)], ['42', '63'])).
% 0.23/0.53  thf('65', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('66', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '24'])).
% 0.23/0.53  thf('67', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf(d4_tmap_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53             ( l1_pre_topc @ B ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.53                 ( m1_subset_1 @
% 0.23/0.53                   C @ 
% 0.23/0.53                   ( k1_zfmisc_1 @
% 0.23/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.53               ( ![D:$i]:
% 0.23/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.23/0.53                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.23/0.53                     ( k2_partfun1 @
% 0.23/0.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.53                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf('68', plain,
% 0.23/0.53      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.23/0.53         ((v2_struct_0 @ X31)
% 0.23/0.53          | ~ (v2_pre_topc @ X31)
% 0.23/0.53          | ~ (l1_pre_topc @ X31)
% 0.23/0.53          | ~ (m1_pre_topc @ X32 @ X33)
% 0.23/0.53          | ((k2_tmap_1 @ X33 @ X31 @ X34 @ X32)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31) @ 
% 0.23/0.53                 X34 @ (u1_struct_0 @ X32)))
% 0.23/0.53          | ~ (m1_subset_1 @ X34 @ 
% 0.23/0.53               (k1_zfmisc_1 @ 
% 0.23/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 0.23/0.53          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 0.23/0.53          | ~ (v1_funct_1 @ X34)
% 0.23/0.53          | ~ (l1_pre_topc @ X33)
% 0.23/0.53          | ~ (v2_pre_topc @ X33)
% 0.23/0.53          | (v2_struct_0 @ X33))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.23/0.53  thf('69', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X1 @ 
% 0.23/0.53             (k1_zfmisc_1 @ 
% 0.23/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.23/0.53          | (v2_struct_0 @ sk_B)
% 0.23/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.23/0.53          | ~ (v1_funct_1 @ X1)
% 0.23/0.53          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.23/0.53                 X1 @ (u1_struct_0 @ X2)))
% 0.23/0.53          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ X0)
% 0.23/0.53          | ~ (v2_pre_topc @ X0)
% 0.23/0.53          | (v2_struct_0 @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.23/0.53  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('72', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('73', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('74', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X1 @ 
% 0.23/0.53             (k1_zfmisc_1 @ 
% 0.23/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.23/0.53          | (v2_struct_0 @ sk_B)
% 0.23/0.53          | ~ (v1_funct_1 @ X1)
% 0.23/0.53          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.23/0.53              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.23/0.53                 (u1_struct_0 @ X2)))
% 0.23/0.53          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ X0)
% 0.23/0.53          | ~ (v2_pre_topc @ X0)
% 0.23/0.53          | (v2_struct_0 @ X0))),
% 0.23/0.53      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.23/0.53  thf('75', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.23/0.53              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53                 sk_D @ (u1_struct_0 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53          | (v2_struct_0 @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['66', '74'])).
% 0.23/0.53  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('78', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '24'])).
% 0.23/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.23/0.53  thf('79', plain,
% 0.23/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.23/0.53          | ~ (v1_funct_1 @ X12)
% 0.23/0.53          | ((k2_partfun1 @ X13 @ X14 @ X12 @ X15) = (k7_relat_1 @ X12 @ X15)))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.23/0.53  thf('80', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.23/0.53  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('82', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.23/0.53           = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.23/0.53  thf('83', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('85', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.23/0.53              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.23/0.53          | (v2_struct_0 @ sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['75', '76', '77', '82', '83', '84'])).
% 0.23/0.53  thf('86', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_B)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.23/0.53            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.23/0.53        | (v2_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['65', '85'])).
% 0.23/0.53  thf('87', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('simplify', [status(thm)], ['62'])).
% 0.23/0.53  thf('88', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_B)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.23/0.53            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.23/0.53        | (v2_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.23/0.53  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('90', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_A)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.23/0.53            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.23/0.53      inference('clc', [status(thm)], ['88', '89'])).
% 0.23/0.53  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('92', plain,
% 0.23/0.53      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.23/0.53         = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.23/0.53      inference('clc', [status(thm)], ['90', '91'])).
% 0.23/0.53  thf('93', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.23/0.53      inference('demod', [status(thm)], ['64', '92'])).
% 0.23/0.53  thf('94', plain,
% 0.23/0.53      ((~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.23/0.53        | ~ (v1_relat_1 @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['39', '93'])).
% 0.23/0.53  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.53  thf('96', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.23/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.23/0.53  thf('97', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['38', '96'])).
% 0.23/0.53  thf('98', plain,
% 0.23/0.53      (![X20 : $i]:
% 0.23/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.23/0.53          | ~ (l1_struct_0 @ X20)
% 0.23/0.53          | (v2_struct_0 @ X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.53  thf('99', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.23/0.53  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf('101', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('demod', [status(thm)], ['99', '100'])).
% 0.23/0.53  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
