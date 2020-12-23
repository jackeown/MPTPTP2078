%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sG3Mti3Hut

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  218 ( 290 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X9
       != ( k1_setfam_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X9 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r2_hidden @ X13 @ ( k1_setfam_1 @ X10 ) )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X12 @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X15: $i] :
      ( ( X15
       != ( k1_setfam_1 @ X10 ) )
      | ( X15 = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','13','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sG3Mti3Hut
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 20 iterations in 0.016s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.44  thf(t4_setfam_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.19/0.44  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(d3_tarski, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      (![X1 : $i, X3 : $i]:
% 0.19/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.44  thf(d1_setfam_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.19/0.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.44       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.19/0.44           ( ![C:$i]:
% 0.19/0.44             ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.44               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.44  thf('3', plain,
% 0.19/0.44      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.44         (((X9) != (k1_setfam_1 @ X10))
% 0.19/0.44          | ~ (r2_hidden @ X12 @ X10)
% 0.19/0.44          | (r2_hidden @ X13 @ X12)
% 0.19/0.44          | ~ (r2_hidden @ X13 @ X9)
% 0.19/0.44          | ((X10) = (k1_xboole_0)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.44         (((X10) = (k1_xboole_0))
% 0.19/0.44          | ~ (r2_hidden @ X13 @ (k1_setfam_1 @ X10))
% 0.19/0.44          | (r2_hidden @ X13 @ X12)
% 0.19/0.44          | ~ (r2_hidden @ X12 @ X10))),
% 0.19/0.44      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.44         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.19/0.44          | ~ (r2_hidden @ X2 @ X0)
% 0.19/0.44          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.19/0.44          | ((X0) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.44  thf('6', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((sk_B) = (k1_xboole_0))
% 0.19/0.44          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_A)
% 0.19/0.44          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['1', '5'])).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X1 : $i, X3 : $i]:
% 0.19/0.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)
% 0.19/0.44        | ((sk_B) = (k1_xboole_0))
% 0.19/0.44        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.19/0.44      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.44  thf('10', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.44      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (![X10 : $i, X15 : $i]:
% 0.19/0.44         (((X15) != (k1_setfam_1 @ X10))
% 0.19/0.44          | ((X15) = (k1_xboole_0))
% 0.19/0.44          | ((X10) != (k1_xboole_0)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.19/0.44  thf('13', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.44      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X1 : $i, X3 : $i]:
% 0.19/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.44  thf(t113_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X5 : $i, X6 : $i]:
% 0.19/0.44         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.44  thf('16', plain,
% 0.19/0.44      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.44      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.44  thf(t152_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.19/0.44      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.19/0.44  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.44      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.44  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.44      inference('sup-', [status(thm)], ['14', '18'])).
% 0.19/0.44  thf('20', plain, ($false),
% 0.19/0.44      inference('demod', [status(thm)], ['0', '11', '13', '19'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
