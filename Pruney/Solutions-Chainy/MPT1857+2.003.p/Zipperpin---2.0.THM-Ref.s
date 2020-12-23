%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cYiYVfvEcP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 911 expanded)
%              Number of leaves         :   25 ( 263 expanded)
%              Depth                    :   18
%              Number of atoms          : 1195 (15207 expanded)
%              Number of equality atoms :   30 ( 685 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t25_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v2_tex_2 @ C @ A ) )
                   => ( v2_tex_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v2_tex_2 @ C @ A ) )
                     => ( v2_tex_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_tex_2 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','9'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( m1_pre_topc @ X13 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('31',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('57',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','42'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( sk_D @ X18 @ X16 @ X17 ) )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      = ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('78',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    = ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( sk_C @ sk_C_1 @ sk_B )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','78'])).

thf('80',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('82',plain,(
    ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('84',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','41'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ X11 @ X12 )
      | ( X11 != X9 )
      | ~ ( m1_pre_topc @ X12 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X12 @ X10 )
      | ( v3_pre_topc @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','42'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v3_pre_topc @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('100',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['90','100','101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['82','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cYiYVfvEcP
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 158 iterations in 0.109s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(t25_tex_2, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( l1_pre_topc @ B ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57               ( ![D:$i]:
% 0.37/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.57                   ( ( ( ( g1_pre_topc @
% 0.37/0.57                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57                         ( g1_pre_topc @
% 0.37/0.57                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.57                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.57                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( l1_pre_topc @ A ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( l1_pre_topc @ B ) =>
% 0.37/0.57              ( ![C:$i]:
% 0.37/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                  ( ![D:$i]:
% 0.37/0.57                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.57                      ( ( ( ( g1_pre_topc @
% 0.37/0.57                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57                            ( g1_pre_topc @
% 0.37/0.57                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.57                          ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.57                        ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t25_tex_2])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain, (((sk_C_1) = (sk_D_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf(d5_tex_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.37/0.57             ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.37/0.57                      ( ![D:$i]:
% 0.37/0.57                        ( ( m1_subset_1 @
% 0.37/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.57                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain, (~ (v2_tex_2 @ sk_D_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('8', plain, (((sk_C_1) = (sk_D_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('9', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('clc', [status(thm)], ['6', '9'])).
% 0.37/0.57  thf(t2_tsep_1, axiom,
% 0.37/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X13 : $i]: ((m1_pre_topc @ X13 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.57  thf(t65_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( l1_pre_topc @ B ) =>
% 0.37/0.57           ( ( m1_pre_topc @ A @ B ) <=>
% 0.37/0.57             ( m1_pre_topc @
% 0.37/0.57               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X7)
% 0.37/0.57          | ~ (m1_pre_topc @ X8 @ X7)
% 0.37/0.57          | (m1_pre_topc @ X8 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.37/0.57          | ~ (l1_pre_topc @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_pre_topc @ X0 @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t59_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @
% 0.37/0.57             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.37/0.57           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X5 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.37/0.57          | (m1_pre_topc @ X5 @ X6)
% 0.37/0.57          | ~ (l1_pre_topc @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57          | (m1_pre_topc @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57          | (m1_pre_topc @ X0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '19'])).
% 0.37/0.57  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('22', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf(t35_borsuk_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X14 @ X15)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X15))
% 0.37/0.57          | ~ (l1_pre_topc @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('26', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf(d10_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_pre_topc @ X0 @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (((m1_pre_topc @ sk_B @ 
% 0.37/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.57  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((m1_pre_topc @ sk_B @ 
% 0.37/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X5 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.37/0.57          | (m1_pre_topc @ X5 @ X6)
% 0.37/0.57          | ~ (l1_pre_topc @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.57  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X14 @ X15)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X15))
% 0.37/0.57          | ~ (l1_pre_topc @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('41', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | (m1_subset_1 @ (sk_D @ X18 @ X16 @ X17) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (r1_tarski @ X18 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('48', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['43', '49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.37/0.57          | (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.57  thf('56', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('57', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.37/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['50', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('60', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '41'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v3_pre_topc @ X19 @ X17)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.37/0.57              != (sk_C @ X16 @ X17))
% 0.37/0.57          | (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_B)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 0.37/0.57              != (sk_C @ X0 @ sk_B))
% 0.37/0.57          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('64', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '41'])).
% 0.37/0.57  thf('65', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '41'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_B)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 0.37/0.57              != (sk_C @ X0 @ sk_B))
% 0.37/0.57          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.37/0.57              != (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.57          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['59', '66'])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.37/0.57            (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.37/0.57            != (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.57        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57             sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['58', '67'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '42'])).
% 0.37/0.57  thf('70', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.37/0.57              (sk_D @ X18 @ X16 @ X17)) = (X18))
% 0.37/0.57          | ~ (r1_tarski @ X18 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.37/0.57              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0))
% 0.37/0.57          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.57  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('74', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.37/0.57              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.37/0.57          (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.37/0.57          = (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.57        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['69', '75'])).
% 0.37/0.57  thf('77', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.37/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.37/0.57         (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.37/0.57         = (sk_C @ sk_C_1 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.57  thf('79', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.37/0.57        | ((sk_C @ sk_C_1 @ sk_B) != (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.57        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57             sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['68', '78'])).
% 0.37/0.57  thf('80', plain,
% 0.37/0.57      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.37/0.57        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.37/0.57      inference('simplify', [status(thm)], ['79'])).
% 0.37/0.57  thf('81', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('82', plain,
% 0.37/0.57      (~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.37/0.57      inference('clc', [status(thm)], ['80', '81'])).
% 0.37/0.57  thf('83', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['50', '57'])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['50', '57'])).
% 0.37/0.57  thf('85', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '41'])).
% 0.37/0.57  thf(t33_tops_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.37/0.57               ( ( v3_pre_topc @ B @ A ) =>
% 0.37/0.57                 ( ![D:$i]:
% 0.37/0.57                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.37/0.57                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('86', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.57          | ~ (v3_pre_topc @ X9 @ X10)
% 0.37/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.57          | (v3_pre_topc @ X11 @ X12)
% 0.37/0.57          | ((X11) != (X9))
% 0.37/0.57          | ~ (m1_pre_topc @ X12 @ X10)
% 0.37/0.57          | ~ (l1_pre_topc @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.37/0.57  thf('87', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X10)
% 0.37/0.57          | ~ (m1_pre_topc @ X12 @ X10)
% 0.37/0.57          | (v3_pre_topc @ X9 @ X12)
% 0.37/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.57          | ~ (v3_pre_topc @ X9 @ X10)
% 0.37/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['86'])).
% 0.37/0.57  thf('88', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.57          | ~ (v3_pre_topc @ X0 @ X1)
% 0.37/0.57          | (v3_pre_topc @ X0 @ sk_B)
% 0.37/0.57          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.37/0.57          | ~ (l1_pre_topc @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['85', '87'])).
% 0.37/0.57  thf('89', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.37/0.57          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57             sk_B)
% 0.37/0.57          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57               X0)
% 0.37/0.57          | ~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['84', '88'])).
% 0.37/0.57  thf('90', plain,
% 0.37/0.57      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.37/0.57        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['83', '89'])).
% 0.37/0.57  thf('91', plain,
% 0.37/0.57      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '42'])).
% 0.37/0.57  thf('92', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('93', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v2_tex_2 @ X16 @ X17)
% 0.37/0.57          | (v3_pre_topc @ (sk_D @ X18 @ X16 @ X17) @ X17)
% 0.37/0.57          | ~ (r1_tarski @ X18 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.57  thf('94', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.37/0.57          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.57  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('96', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('97', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.37/0.57          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.57  thf('98', plain,
% 0.37/0.57      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.37/0.57        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['91', '97'])).
% 0.37/0.57  thf('99', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.37/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('100', plain,
% 0.37/0.57      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['98', '99'])).
% 0.37/0.57  thf('101', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('103', plain,
% 0.37/0.57      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['90', '100', '101', '102'])).
% 0.37/0.57  thf('104', plain, ($false), inference('demod', [status(thm)], ['82', '103'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
