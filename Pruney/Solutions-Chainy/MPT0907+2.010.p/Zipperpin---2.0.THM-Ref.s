%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gDWgci4Uey

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 ( 497 expanded)
%              Number of equality atoms :   41 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('3',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t66_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X7
       != ( k1_mcart_1 @ X7 ) )
      | ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf('5',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
     != ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('9',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X7
       != ( k2_mcart_1 @ X7 ) )
      | ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf('11',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
     != ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('22',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['7','22'])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['5','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gDWgci4Uey
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:51:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 23 iterations in 0.009s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.45  thf(t67_mcart_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.45       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.45          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t67_mcart_1])).
% 0.20/0.45  thf('0', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t1_subset, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.45  thf('3', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf(t66_mcart_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.45       ( ![C:$i]:
% 0.20/0.45         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.45           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X7 @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.45          | ((X7) != (k1_mcart_1 @ X7))
% 0.20/0.45          | ((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t66_mcart_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.45        | ((sk_A) != (k1_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('9', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X7 @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.45          | ((X7) != (k2_mcart_1 @ X7))
% 0.20/0.45          | ((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t66_mcart_1])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.45        | ((sk_A) != (k2_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (((((sk_A) != (sk_A)) | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))))
% 0.20/0.45         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0)))
% 0.20/0.45         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.45      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.45  thf('14', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.45  thf(t113_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.45  thf(t152_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.45  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('20', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['15', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('22', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf('23', plain, (((sk_A) = (k1_mcart_1 @ sk_A))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['7', '22'])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '23'])).
% 0.20/0.45  thf('25', plain, (((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.45  thf('26', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.45  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('28', plain, ($false), inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
