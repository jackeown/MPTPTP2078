%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pNjne42l48

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 343 expanded)
%              Number of leaves         :   23 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  496 (2955 expanded)
%              Number of equality atoms :   45 ( 310 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X22: $i] :
      ( ( k1_subset_1 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('5',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','19'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','19'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    ! [X22: $i] :
      ( ( k1_subset_1 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','11'])).

thf('32',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['46','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pNjne42l48
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 88 iterations in 0.036s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(t38_subset_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.19/0.49        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.19/0.49         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.19/0.49        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.19/0.49       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('4', plain, (![X22 : $i]: ((k1_subset_1 @ X22) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.19/0.49         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.19/0.49             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('10', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.19/0.49       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.19/0.49       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('13', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['3', '11', '12'])).
% 0.19/0.49  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d5_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.49  thf(t7_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X10 : $i]:
% 0.19/0.49         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf(d4_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.49          | (r2_hidden @ X4 @ X2)
% 0.19/0.49          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.49         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.49          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (((r2_hidden @ (sk_B @ sk_B_1) @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.19/0.49        | ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.19/0.49            = (k1_xboole_0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['20', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (((r2_hidden @ (sk_B @ sk_B_1) @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.19/0.49        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.19/0.49         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('29', plain, (![X22 : $i]: ((k1_subset_1 @ X22) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['3', '11'])).
% 0.19/0.49  thf('32', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((r2_hidden @ (sk_B @ sk_B_1) @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      ((r2_hidden @ (sk_B @ sk_B_1) @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X10 : $i]:
% 0.19/0.49         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.49          | ~ (r2_hidden @ X0 @ X2)
% 0.19/0.49          | (r2_hidden @ X0 @ X3)
% 0.19/0.49          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.19/0.49          | ~ (r2_hidden @ X0 @ X2)
% 0.19/0.49          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X0) = (k1_xboole_0))
% 0.19/0.49          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.19/0.49          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (((r2_hidden @ (sk_B @ sk_B_1) @ 
% 0.19/0.49         (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.19/0.49        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '38'])).
% 0.19/0.49  thf('40', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((r2_hidden @ (sk_B @ sk_B_1) @ 
% 0.19/0.49        (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.49         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.49  thf('43', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf(t3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ X9)
% 0.19/0.49          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_xboole_0 @ sk_B_1 @ X0) | ~ (r2_hidden @ (sk_B @ sk_B_1) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, (~ (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '45'])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('48', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.19/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.49  thf(t85_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X19 @ X20)
% 0.19/0.49          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.49  thf('51', plain, ($false), inference('demod', [status(thm)], ['46', '50'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
