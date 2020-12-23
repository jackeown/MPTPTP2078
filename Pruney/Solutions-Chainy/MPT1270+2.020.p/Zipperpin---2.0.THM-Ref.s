%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VyCewdwBbU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 152 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  424 (1534 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ X6 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ ( k2_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( ( k7_subset_1 @ X4 @ X3 @ X5 )
        = ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_tops_1 @ X9 @ X8 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tops_1 @ X8 @ X9 )
      | ( ( k1_tops_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('38',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','24','37'])).

thf('39',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['26','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VyCewdwBbU
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:20:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 31 iterations in 0.016s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(t88_tops_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( l1_pre_topc @ A ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.20/0.50       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t74_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( k1_tops_1 @ A @ B ) =
% 0.20/0.50             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50          | ((k1_tops_1 @ X7 @ X6)
% 0.20/0.50              = (k7_subset_1 @ (u1_struct_0 @ X7) @ X6 @ (k2_tops_1 @ X7 @ X6)))
% 0.20/0.50          | ~ (l1_pre_topc @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.20/0.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.50               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.50          | ((k7_subset_1 @ X4 @ X3 @ X5) = (k4_xboole_0 @ X3 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((k1_tops_1 @ sk_A @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.50         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf(l32_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t84_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ((k1_tops_1 @ X9 @ X8) != (k1_xboole_0))
% 0.20/0.50          | (v2_tops_1 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.50         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A))
% 0.20/0.50         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '24'])).
% 0.20/0.50  thf('26', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((k1_tops_1 @ sk_A @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '9'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v2_tops_1 @ X8 @ X9)
% 0.20/0.50          | ((k1_tops_1 @ X9 @ X8) = (k1_xboole_0))
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.50       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf('38', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '24', '37'])).
% 0.20/0.50  thf('39', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '39'])).
% 0.20/0.50  thf('41', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('42', plain, ($false), inference('demod', [status(thm)], ['26', '41'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
