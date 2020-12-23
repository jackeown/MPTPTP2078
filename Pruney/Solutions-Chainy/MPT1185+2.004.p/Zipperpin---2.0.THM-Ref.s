%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7he42RVLCd

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 153 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  520 (1472 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r3_orders_1_type,type,(
    r3_orders_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ~ ( v4_orders_2 @ X9 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
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

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_orders_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r8_relat_2 @ C @ A )
          & ( r1_tarski @ B @ A ) )
       => ( r8_relat_2 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( r8_relat_2 @ X22 @ X20 )
      | ~ ( r8_relat_2 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_orders_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_relat_2 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v6_orders_2 @ X7 @ X8 )
      | ( r7_relat_2 @ ( u1_orders_2 @ X8 ) @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('18',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v6_orders_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t92_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r7_relat_2 @ B @ A )
      <=> ( ( r1_relat_2 @ B @ A )
          & ( r6_relat_2 @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r7_relat_2 @ X15 @ X16 )
      | ( r1_relat_2 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf(d8_orders_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r3_orders_1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_relat_2 @ X11 @ X12 )
      | ~ ( r8_relat_2 @ X11 @ X12 )
      | ~ ( r4_relat_2 @ X11 @ X12 )
      | ~ ( r6_relat_2 @ X11 @ X12 )
      | ( r3_orders_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_orders_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('30',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r7_relat_2 @ X15 @ X16 )
      | ( r6_relat_2 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( ~ ( v5_orders_2 @ X10 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t94_orders_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r4_relat_2 @ C @ A )
          & ( r1_tarski @ B @ A ) )
       => ( r4_relat_2 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( r4_relat_2 @ X19 @ X17 )
      | ~ ( r4_relat_2 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_orders_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r4_relat_2 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','48'])).

thf('50',plain,(
    ~ ( r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','51'])).

thf('53',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7he42RVLCd
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:59:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 46 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.20/0.47  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(r3_orders_1_type, type, r3_orders_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(dt_u1_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( m1_subset_1 @
% 0.20/0.47         ( u1_orders_2 @ A ) @ 
% 0.20/0.47         ( k1_zfmisc_1 @
% 0.20/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X14 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_orders_2 @ X14) @ 
% 0.20/0.47           (k1_zfmisc_1 @ 
% 0.20/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14))))
% 0.20/0.47          | ~ (l1_orders_2 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.47          | (v1_relat_1 @ X3)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ 
% 0.20/0.47               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d5_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ( v4_orders_2 @ A ) <=>
% 0.20/0.47         ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X9 : $i]:
% 0.20/0.47         (~ (v4_orders_2 @ X9)
% 0.20/0.47          | (r8_relat_2 @ (u1_orders_2 @ X9) @ (u1_struct_0 @ X9))
% 0.20/0.47          | ~ (l1_orders_2 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_orders_2])).
% 0.20/0.47  thf(t136_orders_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( v6_orders_2 @ B @ A ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( v6_orders_2 @ B @ A ) & 
% 0.20/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47              ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t136_orders_2])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t95_orders_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( ( r8_relat_2 @ C @ A ) & ( r1_tarski @ B @ A ) ) =>
% 0.20/0.47         ( r8_relat_2 @ C @ B ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X20 @ X21)
% 0.20/0.47          | ~ (v1_relat_1 @ X22)
% 0.20/0.47          | (r8_relat_2 @ X22 @ X20)
% 0.20/0.47          | ~ (r8_relat_2 @ X22 @ X21))),
% 0.20/0.47      inference('cnf', [status(esa)], [t95_orders_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r8_relat_2 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (r8_relat_2 @ X0 @ sk_B)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.47  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d11_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v6_orders_2 @ B @ A ) <=>
% 0.20/0.47             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.47          | ~ (v6_orders_2 @ X7 @ X8)
% 0.20/0.47          | (r7_relat_2 @ (u1_orders_2 @ X8) @ X7)
% 0.20/0.47          | ~ (l1_orders_2 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (v6_orders_2 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, ((v6_orders_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, ((r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.47  thf(t92_orders_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r7_relat_2 @ B @ A ) <=>
% 0.20/0.47         ( ( r1_relat_2 @ B @ A ) & ( r6_relat_2 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (r7_relat_2 @ X15 @ X16)
% 0.20/0.47          | (r1_relat_2 @ X15 @ X16)
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t92_orders_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '23'])).
% 0.20/0.47  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, ((r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf(d8_orders_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( r3_orders_1 @ A @ B ) <=>
% 0.20/0.47           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.20/0.47             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r1_relat_2 @ X11 @ X12)
% 0.20/0.47          | ~ (r8_relat_2 @ X11 @ X12)
% 0.20/0.47          | ~ (r4_relat_2 @ X11 @ X12)
% 0.20/0.47          | ~ (r6_relat_2 @ X11 @ X12)
% 0.20/0.47          | (r3_orders_1 @ X11 @ X12)
% 0.20/0.47          | ~ (v1_relat_1 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_orders_1])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('30', plain, ((r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (r7_relat_2 @ X15 @ X16)
% 0.20/0.47          | (r6_relat_2 @ X15 @ X16)
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t92_orders_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.47  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain, ((r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d6_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ( v5_orders_2 @ A ) <=>
% 0.20/0.47         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         (~ (v5_orders_2 @ X10)
% 0.20/0.47          | (r4_relat_2 @ (u1_orders_2 @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.47          | ~ (l1_orders_2 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.20/0.47  thf('39', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t94_orders_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( ( r4_relat_2 @ C @ A ) & ( r1_tarski @ B @ A ) ) =>
% 0.20/0.47         ( r4_relat_2 @ C @ B ) ) ))).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X17 @ X18)
% 0.20/0.47          | ~ (v1_relat_1 @ X19)
% 0.20/0.47          | (r4_relat_2 @ X19 @ X17)
% 0.20/0.47          | ~ (r4_relat_2 @ X19 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_orders_1])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r4_relat_2 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (r4_relat_2 @ X0 @ sk_B)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.47  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '45'])).
% 0.20/0.47  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('48', plain, ((r4_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '48'])).
% 0.20/0.47  thf('50', plain, (~ (r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      ((~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.47  thf('52', plain, (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['14', '51'])).
% 0.20/0.47  thf('53', plain, (~ (l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '52'])).
% 0.20/0.47  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
