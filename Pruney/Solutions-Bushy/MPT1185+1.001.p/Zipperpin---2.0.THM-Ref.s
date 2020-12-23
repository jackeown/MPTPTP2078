%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1185+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WXazfMJXwc

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 141 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  501 (1396 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_1_type,type,(
    r3_orders_1: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ~ ( v4_orders_2 @ X5 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf(t136_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ( v6_orders_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ( v6_orders_2 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t136_orders_2])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t95_orders_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r8_relat_2 @ C @ A )
          & ( r1_tarski @ B @ A ) )
       => ( r8_relat_2 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( r8_relat_2 @ X21 @ X19 )
      | ~ ( r8_relat_2 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t95_orders_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_relat_2 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v6_orders_2 @ X3 @ X4 )
      | ( r7_relat_2 @ ( u1_orders_2 @ X4 ) @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('16',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v6_orders_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t92_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r7_relat_2 @ B @ A )
      <=> ( ( r1_relat_2 @ B @ A )
          & ( r6_relat_2 @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r7_relat_2 @ X14 @ X15 )
      | ( r1_relat_2 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf(d8_orders_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r3_orders_1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_relat_2 @ X7 @ X8 )
      | ~ ( r8_relat_2 @ X7 @ X8 )
      | ~ ( r4_relat_2 @ X7 @ X8 )
      | ~ ( r6_relat_2 @ X7 @ X8 )
      | ( r3_orders_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_orders_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('28',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r7_relat_2 @ X14 @ X15 )
      | ( r6_relat_2 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ~ ( v5_orders_2 @ X6 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t94_orders_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r4_relat_2 @ C @ A )
          & ( r1_tarski @ B @ A ) )
       => ( r4_relat_2 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( r4_relat_2 @ X18 @ X16 )
      | ~ ( r4_relat_2 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_orders_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r4_relat_2 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','46'])).

thf('48',plain,(
    ~ ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','49'])).

thf('51',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).


%------------------------------------------------------------------------------
