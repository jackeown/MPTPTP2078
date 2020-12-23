%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UGQUNEqQg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 244 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  362 (2344 expanded)
%              Number of equality atoms :   48 ( 454 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ ( k1_tarski @ X20 ) )
      | ( X19
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X20: $i] :
      ( r1_tarski @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
        = ( k1_tarski @ X18 ) )
      | ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['5','16','17'])).

thf('19',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('31',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('36',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('37',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UGQUNEqQg
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 174 iterations in 0.066s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(t44_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.53  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l3_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((r1_tarski @ X19 @ (k1_tarski @ X20)) | ((X19) != (k1_tarski @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X20 : $i]: (r1_tarski @ (k1_tarski @ X20) @ (k1_tarski @ X20))),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.53  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t11_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.53  thf('8', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (((X19) = (k1_tarski @ X18))
% 0.21/0.53          | ((X19) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X19 @ (k1_tarski @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.53  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('18', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['5', '16', '17'])).
% 0.21/0.53  thf('19', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf(t4_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.53       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.53           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ sk_B @ X0)
% 0.21/0.53           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(t10_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X1 @ X2) | (r1_tarski @ X1 @ (k2_xboole_0 @ X3 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf(t12_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_B))
% 0.21/0.53           = (k2_xboole_0 @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((k2_xboole_0 @ sk_B @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['21', '28'])).
% 0.21/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.53  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.53  thf('31', plain, (((sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('36', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('37', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.53  thf('39', plain, ((((sk_C) = (sk_B)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '38'])).
% 0.21/0.53  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain, (((sk_B) != (sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['39', '40', '41'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
