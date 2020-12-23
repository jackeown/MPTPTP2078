%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IjSmq7CZ33

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 178 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  503 (1331 expanded)
%              Number of equality atoms :   52 ( 142 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['11','34','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['9','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','23'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X26 @ X25 ) @ ( k3_subset_1 @ X26 @ X27 ) )
      | ( r1_tarski @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['38','44'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('47',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','34'])).

thf('53',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IjSmq7CZ33
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 198 iterations in 0.096s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(t39_subset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.56         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.56            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.56        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf(t12_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      ((((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      ((((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d5_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.56        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.56       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('split', [status(esa)], ['10'])).
% 0.20/0.56  thf(dt_k2_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.56  thf('13', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('14', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.56  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.56  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.56  thf(t46_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['19', '22'])).
% 0.20/0.56  thf('24', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '23'])).
% 0.20/0.56  thf('25', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['10'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '31'])).
% 0.20/0.56  thf('33', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.56       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.56       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('36', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['11', '34', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['9', '36'])).
% 0.20/0.56  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '23'])).
% 0.20/0.56  thf(t31_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56           ( ( r1_tarski @ B @ C ) <=>
% 0.20/0.56             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.20/0.56          | ~ (r1_tarski @ (k3_subset_1 @ X26 @ X25) @ 
% 0.20/0.56               (k3_subset_1 @ X26 @ X27))
% 0.20/0.56          | (r1_tarski @ X27 @ X25)
% 0.20/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.56          | (r1_tarski @ X0 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('43', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.56  thf('45', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '44'])).
% 0.20/0.56  thf(t45_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.56       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (((X6) = (k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))
% 0.20/0.56          | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((sk_A) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain, (((sk_A) = (sk_B))),
% 0.20/0.56      inference('sup+', [status(thm)], ['37', '47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.56         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('split', [status(esa)], ['10'])).
% 0.20/0.56  thf('50', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('52', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['11', '34'])).
% 0.20/0.56  thf('53', plain, (((sk_B) != (sk_A))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['48', '53'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
