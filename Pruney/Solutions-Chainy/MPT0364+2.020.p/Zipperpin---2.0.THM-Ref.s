%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7owDLMUUq

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 147 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  507 (1428 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('48',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['14','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7owDLMUUq
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 77 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(t44_subset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.20/0.52             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.20/0.52                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.20/0.52        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.20/0.52       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.52        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf(t85_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.52          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.20/0.52         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.52         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.52  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.20/0.52  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.20/0.52  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.52         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['21', '28'])).
% 0.20/0.52  thf(t36_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.52  thf('31', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.20/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf(t86_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.20/0.52       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.52          | ~ (r1_xboole_0 @ X5 @ X7)
% 0.20/0.52          | (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.20/0.52           | ~ (r1_tarski @ sk_B @ X0)))
% 0.20/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.52           | ~ (r1_tarski @ sk_B @ X0)))
% 0.20/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.20/0.52       ((r1_tarski @ sk_B @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('38', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '12', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.52          | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '39'])).
% 0.20/0.52  thf('41', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.20/0.52         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((sk_C) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['45', '52'])).
% 0.20/0.52  thf('54', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '53'])).
% 0.20/0.52  thf('55', plain, ($false), inference('demod', [status(thm)], ['14', '54'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
