%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XgteOtJ6N1

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  517 (1349 expanded)
%              Number of equality atoms :   55 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k3_subset_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('35',plain,(
    ! [X19: $i] :
      ( X19
      = ( k3_subset_1 @ X19 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['31','35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','46'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['24','49'])).

thf('51',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('53',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','11'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XgteOtJ6N1
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 77 iterations in 0.029s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.45  thf(t38_subset_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.45         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.45            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.19/0.45        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.45         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.45      inference('split', [status(esa)], ['0'])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.19/0.45        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.19/0.45       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.45      inference('split', [status(esa)], ['2'])).
% 0.19/0.45  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.45  thf('4', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('split', [status(esa)], ['0'])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.45         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.45      inference('split', [status(esa)], ['2'])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.45         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.45             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.45  thf('10', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.45       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.45      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.45       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.45      inference('split', [status(esa)], ['0'])).
% 0.19/0.45  thf('13', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.45      inference('sat_resolution*', [status(thm)], ['3', '11', '12'])).
% 0.19/0.45  thf('14', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.19/0.45      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.45  thf(t28_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.45  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d5_subset_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      (![X17 : $i, X18 : $i]:
% 0.19/0.45         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.19/0.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.19/0.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.45  thf('20', plain,
% 0.19/0.45      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.45  thf(t100_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.45  thf('21', plain,
% 0.19/0.45      (![X6 : $i, X7 : $i]:
% 0.19/0.45         ((k4_xboole_0 @ X6 @ X7)
% 0.19/0.45           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.45  thf('22', plain,
% 0.19/0.45      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.19/0.45         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.19/0.45      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.45  thf(t92_xboole_1, axiom,
% 0.19/0.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.45  thf('23', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.45  thf('25', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t35_subset_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45       ( ![C:$i]:
% 0.19/0.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.19/0.45             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.45  thf('27', plain,
% 0.19/0.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.45         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.19/0.45          | (r1_tarski @ X20 @ (k3_subset_1 @ X21 @ X22))
% 0.19/0.45          | ~ (r1_tarski @ X22 @ (k3_subset_1 @ X21 @ X20))
% 0.19/0.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.45          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.45          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.45  thf('29', plain,
% 0.19/0.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.45  thf('30', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.45          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.19/0.45          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.19/0.45      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.45  thf('31', plain,
% 0.19/0.45      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.19/0.45        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['25', '30'])).
% 0.19/0.45  thf(t22_subset_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.19/0.45  thf('32', plain,
% 0.19/0.45      (![X19 : $i]:
% 0.19/0.45         ((k2_subset_1 @ X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.19/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.45  thf('33', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.45  thf('34', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.45  thf('35', plain, (![X19 : $i]: ((X19) = (k3_subset_1 @ X19 @ k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.45  thf(t4_subset_1, axiom,
% 0.19/0.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      (![X23 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.19/0.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.45  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.45      inference('demod', [status(thm)], ['31', '35', '36'])).
% 0.19/0.45  thf('38', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.45  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.45  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.45  thf('40', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.45  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.45  thf(l97_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.19/0.45  thf('42', plain,
% 0.19/0.45      (![X4 : $i, X5 : $i]:
% 0.19/0.45         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.19/0.45  thf('43', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.45      inference('sup+', [status(thm)], ['41', '42'])).
% 0.19/0.45  thf('44', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.45  thf('45', plain,
% 0.19/0.45      (![X6 : $i, X7 : $i]:
% 0.19/0.45         ((k4_xboole_0 @ X6 @ X7)
% 0.19/0.45           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.45  thf('46', plain,
% 0.19/0.45      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.45      inference('sup+', [status(thm)], ['44', '45'])).
% 0.19/0.45  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['43', '46'])).
% 0.19/0.45  thf(t83_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.45  thf('48', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i]:
% 0.19/0.45         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.45  thf('49', plain,
% 0.19/0.45      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.45  thf('50', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.45      inference('sup+', [status(thm)], ['24', '49'])).
% 0.19/0.45  thf('51', plain,
% 0.19/0.45      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.19/0.45         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('split', [status(esa)], ['2'])).
% 0.19/0.45  thf('52', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.45  thf('53', plain,
% 0.19/0.45      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.45      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.45  thf('54', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.45      inference('sat_resolution*', [status(thm)], ['3', '11'])).
% 0.19/0.45  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.45      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.19/0.45  thf('56', plain, ($false),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
