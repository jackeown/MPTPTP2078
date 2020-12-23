%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnW5jSOAGs

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 170 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  573 (2037 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t105_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( ( v5_tops_1 @ B @ A )
            <=> ( v6_tops_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v4_pre_topc @ B @ A ) )
             => ( ( v5_tops_1 @ B @ A )
              <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t105_tops_1])).

thf('0',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10
       != ( k1_tops_1 @ X11 @ ( k2_pre_topc @ X11 @ X10 ) ) )
      | ( v6_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ X6 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['12','36'])).

thf('38',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( $false
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8
       != ( k2_pre_topc @ X9 @ ( k1_tops_1 @ X9 @ X8 ) ) )
      | ( v5_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['32','35'])).

thf('46',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('47',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v5_tops_1 @ sk_B @ sk_A )
   <= ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['39','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnW5jSOAGs
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 46 iterations in 0.023s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(t105_tops_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.21/0.49             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.21/0.49                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v6_tops_1 @ B @ A ) <=>
% 0.21/0.49             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ((X10) != (k1_tops_1 @ X11 @ (k2_pre_topc @ X11 @ X10)))
% 0.21/0.49          | (v6_tops_1 @ X10 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v6_tops_1 @ sk_B @ sk_A)
% 0.21/0.49        | ((sk_B) != (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t52_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.49             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.49               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.49          | ~ (v4_pre_topc @ X4 @ X5)
% 0.21/0.49          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.21/0.49          | ~ (l1_pre_topc @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.49        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.49             ( k3_subset_1 @
% 0.21/0.49               ( u1_struct_0 @ A ) @ 
% 0.21/0.49               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | ((k1_tops_1 @ X7 @ X6)
% 0.21/0.49              = (k3_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.49                 (k2_pre_topc @ X7 @ (k3_subset_1 @ (u1_struct_0 @ X7) @ X6))))
% 0.21/0.49          | ~ (l1_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.49            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49               (k2_pre_topc @ sk_A @ 
% 0.21/0.49                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.49          | ~ (v4_pre_topc @ X4 @ X5)
% 0.21/0.49          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.21/0.49          | ~ (l1_pre_topc @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t30_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | ~ (v3_pre_topc @ X12 @ X13)
% 0.21/0.49          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.21/0.49          | ~ (l1_pre_topc @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['32', '35'])).
% 0.21/0.49  thf('37', plain, (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '36'])).
% 0.21/0.49  thf('38', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain, (($false) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d7_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v5_tops_1 @ B @ A ) <=>
% 0.21/0.49             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | ((X8) != (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 0.21/0.49          | (v5_tops_1 @ X8 @ X9)
% 0.21/0.49          | ~ (l1_pre_topc @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v5_tops_1 @ sk_B @ sk_A)
% 0.21/0.49        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((v5_tops_1 @ sk_B @ sk_A)
% 0.21/0.49        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['32', '35'])).
% 0.21/0.49  thf('46', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('47', plain, (((v5_tops_1 @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.49  thf('48', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('50', plain, (((v5_tops_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('52', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain, ($false),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['39', '52'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
