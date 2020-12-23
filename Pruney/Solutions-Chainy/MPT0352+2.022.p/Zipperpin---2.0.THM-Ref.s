%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UzxQnKnfxw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 213 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  544 (2296 expanded)
%              Number of equality atoms :   20 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['9','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['8','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['9','37','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('51',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['39','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UzxQnKnfxw
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 74 iterations in 0.028s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(t31_subset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49           ( ( r1_tarski @ B @ C ) <=>
% 0.22/0.49             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49              ( ( r1_tarski @ B @ C ) <=>
% 0.22/0.49                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49           (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.49        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49           (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.49         <= (~
% 0.22/0.49             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d5_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.22/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.22/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.22/0.49           (k4_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.49         <= (~
% 0.22/0.49             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '4', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.49       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.22/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.22/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.22/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.49         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.49        | (r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['23', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf(t44_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.22/0.49       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.22/0.49          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf(t43_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.22/0.49       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.49          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.22/0.49          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) @ sk_C))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['22', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ~
% 0.22/0.49       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['9', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['8', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['24'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['24'])).
% 0.22/0.49  thf('42', plain, (((r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['9', '37', '41'])).
% 0.22/0.49  thf('43', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '21'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.22/0.49          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_tarski @ sk_B @ X0)
% 0.22/0.49          | (r1_tarski @ sk_A @ 
% 0.22/0.49             (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      ((r1_tarski @ sk_A @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.49          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.49  thf('52', plain, ($false), inference('demod', [status(thm)], ['39', '51'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
