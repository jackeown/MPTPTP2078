%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8TPXhqy4P3

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 122 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  458 (1214 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('6',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X17 @ X16 ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X13 )
      | ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['23','39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['14','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8TPXhqy4P3
% 0.13/0.37  % Computer   : n003.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:05:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 171 iterations in 0.056s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(t44_subset_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ![C:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.23/0.54             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i]:
% 0.23/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54          ( ![C:$i]:
% 0.23/0.54            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.23/0.54                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.23/0.54        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.23/0.54       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (((r1_tarski @ sk_B @ sk_C)
% 0.23/0.54        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.54      inference('split', [status(esa)], ['3'])).
% 0.23/0.54  thf(t85_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X8 @ X9)
% 0.23/0.54          | (r1_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))
% 0.23/0.54         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d5_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.23/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.54         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      ((~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.23/0.54         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.23/0.54       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.23/0.54  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.23/0.54  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.23/0.54  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.23/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf(t31_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ![C:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54           ( ( r1_tarski @ B @ C ) <=>
% 0.23/0.54             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.23/0.54          | ~ (r1_tarski @ (k3_subset_1 @ X17 @ X16) @ 
% 0.23/0.54               (k3_subset_1 @ X17 @ X18))
% 0.23/0.54          | (r1_tarski @ X18 @ X16)
% 0.23/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.23/0.54             (k3_subset_1 @ sk_A @ X0))
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54          | (r1_tarski @ X0 @ sk_C)
% 0.23/0.54          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.54  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.23/0.54             (k3_subset_1 @ sk_A @ X0))
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54          | (r1_tarski @ X0 @ sk_C))),
% 0.23/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.23/0.54           (k4_xboole_0 @ sk_A @ sk_B))
% 0.23/0.54        | (r1_tarski @ sk_B @ sk_C)
% 0.23/0.54        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['17', '22'])).
% 0.23/0.54  thf(d10_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.54  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.23/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.23/0.54  thf(t106_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.23/0.54       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.54         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.54         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('split', [status(esa)], ['3'])).
% 0.23/0.54  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.54      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))
% 0.23/0.54         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf(t86_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.23/0.54       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X11 @ X12)
% 0.23/0.54          | ~ (r1_xboole_0 @ X11 @ X13)
% 0.23/0.54          | (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.23/0.54           | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ X0)))
% 0.23/0.54         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      ((![X0 : $i]:
% 0.23/0.54          ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.23/0.54           | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ X0)))
% 0.23/0.54         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.54      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.23/0.54       ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.54      inference('split', [status(esa)], ['3'])).
% 0.23/0.54  thf('37', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['2', '12', '36'])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.23/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ X0))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['27', '38'])).
% 0.23/0.54  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('41', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.23/0.54      inference('demod', [status(thm)], ['23', '39', '40'])).
% 0.23/0.54  thf('42', plain, ($false), inference('demod', [status(thm)], ['14', '41'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
