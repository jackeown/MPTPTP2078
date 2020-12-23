%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PbZwz9sk4u

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  83 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  272 ( 649 expanded)
%              Number of equality atoms :   41 ( 105 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) )
        = ( k1_tarski @ X26 ) )
      | ( X26 = X27 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 != X25 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X25 ) )
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) )
     != ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
     != ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B_1 )
     != ( k1_tarski @ sk_B_1 ) )
    | ( sk_B_1 = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_A ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) )
     != ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('12',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('15',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PbZwz9sk4u
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 221 iterations in 0.078s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(t20_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.53         ( k1_tarski @ A ) ) <=>
% 0.19/0.53       ( ( A ) != ( B ) ) ))).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27))
% 0.19/0.53            = (k1_tarski @ X26))
% 0.19/0.53          | ((X26) = (X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.53  thf(t24_zfmisc_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.53       ( ( A ) = ( B ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i]:
% 0.19/0.53        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.53          ( ( A ) = ( B ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.19/0.53  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(l3_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X22 : $i, X23 : $i]:
% 0.19/0.53         (((X23) = (k1_tarski @ X22))
% 0.19/0.53          | ((X23) = (k1_xboole_0))
% 0.19/0.53          | ~ (r1_tarski @ X23 @ (k1_tarski @ X22)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.53        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]:
% 0.19/0.53         (((X26) != (X25))
% 0.19/0.53          | ((k4_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X25))
% 0.19/0.53              != (k1_tarski @ X26)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X25 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))
% 0.19/0.53           != (k1_tarski @ X25))),
% 0.19/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.19/0.53          != (k1_tarski @ sk_B_1))
% 0.19/0.53        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      ((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.19/0.53        | ((sk_B_1) = (sk_A))
% 0.19/0.53        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B_1) = (sk_A)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.53  thf('9', plain, (((sk_A) != (sk_B_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X25 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))
% 0.19/0.53           != (k1_tarski @ X25))),
% 0.19/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('14', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.19/0.53  thf(t7_xboole_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.53  thf(d5_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.53       ( ![D:$i]:
% 0.19/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.53          | (r2_hidden @ X4 @ X1)
% 0.19/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.53         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.53          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.53          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.19/0.53          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['19', '23'])).
% 0.19/0.53  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.53  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '25'])).
% 0.19/0.53  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
