%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xf5YiUwtr4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (1747 expanded)
%              Number of leaves         :   26 ( 497 expanded)
%              Depth                    :   20
%              Number of atoms          : 1019 (28100 expanded)
%              Number of equality atoms :   29 ( 317 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t18_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_compts_1 @ B @ A )
                    & ( r1_tarski @ C @ B )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( v2_compts_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_compts_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('6',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ( ( sk_D @ X16 @ X14 )
        = X16 )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,
    ( ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_C ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','36'])).

thf('38',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t17_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_compts_1 @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v2_compts_1 @ B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_compts_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X16 @ X14 ) @ X14 )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_C ),
    inference(clc,[status(thm)],['34','35'])).

thf('61',plain,(
    ~ ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t34_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v4_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_C @ X0 )
      | ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('71',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( X18 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','72'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('86',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18 != k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('88',plain,(
    ! [X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X19 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('92',plain,(
    v2_compts_1 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['83','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xf5YiUwtr4
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 76 iterations in 0.048s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(t18_compts_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.53                   ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.53                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                  ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.53                      ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.53                    ( v2_compts_1 @ C @ A ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t18_compts_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d10_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.20/0.53                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ((X2) != (k1_pre_topc @ X1 @ X0))
% 0.20/0.53          | ((k2_struct_0 @ X2) = (X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.53          | ~ (v1_pre_topc @ X2)
% 0.20/0.53          | ~ (l1_pre_topc @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X1)
% 0.20/0.53          | ~ (v1_pre_topc @ (k1_pre_topc @ X1 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_pre_topc @ X1 @ X0) @ X1)
% 0.20/0.53          | ((k2_struct_0 @ (k1_pre_topc @ X1 @ X0)) = (X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_pre_topc, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.53         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X3)
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.53          | (v1_pre_topc @ (k1_pre_topc @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X3)
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.53          | (m1_pre_topc @ (k1_pre_topc @ X3 @ X4) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t11_compts_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.20/0.53                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.20/0.53                   ( ![D:$i]:
% 0.20/0.53                     ( ( m1_subset_1 @
% 0.20/0.53                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ X16 @ X14) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.53          | (v2_compts_1 @ X16 @ X15)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ sk_C @ X0) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ sk_C @ X0) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.53  thf('23', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('25', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.20/0.53          | ((sk_D @ X16 @ X14) = (X16))
% 0.20/0.53          | (v2_compts_1 @ X16 @ X15)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | ((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.53  thf('32', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.20/0.53  thf('35', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain, (((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '24', '36'])).
% 0.20/0.53  thf('38', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf(t17_compts_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v1_compts_1 @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.53             ( v2_compts_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | (v2_compts_1 @ X20 @ X21)
% 0.20/0.53          | ~ (v4_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (v1_compts_1 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t17_compts_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '46'])).
% 0.20/0.53  thf('48', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.20/0.53          | ~ (v2_compts_1 @ (sk_D @ X16 @ X14) @ X14)
% 0.20/0.53          | (v2_compts_1 @ X16 @ X15)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.53          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.20/0.53          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | ~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.53             (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '53'])).
% 0.20/0.53  thf('55', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.53           (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.53  thf('58', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.53          (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain, (((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('61', plain, (~ (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((~ (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['47', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf(t34_tops_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.53                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.53          | ~ (v4_pre_topc @ X10 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.53          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.53          | ((X12) != (X10))
% 0.20/0.53          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.53          | ~ (l1_pre_topc @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_tops_2])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X11)
% 0.20/0.53          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.53          | (v4_pre_topc @ X10 @ X13)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.53          | ~ (v4_pre_topc @ X10 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (v4_pre_topc @ sk_C @ X0)
% 0.20/0.53          | (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.53        | (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '67'])).
% 0.20/0.53  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('71', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain, ((v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.20/0.53  thf('73', plain, (~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t12_compts_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53               ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.53                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 0.20/0.53             ( ( v2_pre_topc @ A ) =>
% 0.20/0.53               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53                 ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.53                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ((X18) = (k1_xboole_0))
% 0.20/0.53          | (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.20/0.53          | ~ (v2_compts_1 @ X18 @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.53        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.20/0.53  thf('81', plain, (~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '72'])).
% 0.20/0.53  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain, (~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['73', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ((X18) != (k1_xboole_0))
% 0.20/0.53          | (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.20/0.53          | ~ (v2_compts_1 @ X18 @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X19 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_compts_1 @ k1_xboole_0 @ X19)
% 0.20/0.53          | (v1_compts_1 @ (k1_pre_topc @ X19 @ k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['87'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.53        | ~ (v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '88'])).
% 0.20/0.53  thf('90', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('91', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('92', plain, ((v2_compts_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.53  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('94', plain, ((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['89', '92', '93'])).
% 0.20/0.53  thf('95', plain, ($false), inference('demod', [status(thm)], ['83', '94'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
