%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.poipHyYvSL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 105 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  321 ( 963 expanded)
%              Number of equality atoms :   47 ( 138 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('0',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X8 ) @ X9 )
        = np__1 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X5 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( ( k1_relat_1 @ X10 )
       != sk_A )
      | ( ( k1_relat_1 @ X11 )
       != sk_A )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('9',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( sk_C @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_funct_1 @ ( sk_C @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( sk_C @ X1 @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X5 @ X6 ) @ X7 )
        = X5 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ sk_A ) @ ( sk_B @ sk_A ) )
        = X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( np__1 = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( k1_xboole_0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('30',plain,(
    np__1 != np__1 ),
    inference(demod,[status(thm)],['0','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.poipHyYvSL
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:22:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 50 iterations in 0.041s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.51  thf(np__1_type, type, np__1: $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.51  thf(t16_funct_1, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ![B:$i]:
% 0.23/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.23/0.51                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.23/0.51                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.23/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ![B:$i]:
% 0.23/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.51              ( ![C:$i]:
% 0.23/0.51                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.23/0.51                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.23/0.51                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.23/0.51          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.23/0.51  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d1_xboole_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.51  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ?[B:$i]:
% 0.23/0.51       ( ( ![C:$i]:
% 0.23/0.51           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.23/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.23/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (((k1_funct_1 @ (sk_B_1 @ X8) @ X9) = (np__1))
% 0.23/0.51          | ~ (r2_hidden @ X9 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_xboole_0 @ X0)
% 0.23/0.51          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ?[C:$i]:
% 0.23/0.51       ( ( ![D:$i]:
% 0.23/0.51           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.23/0.51         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.23/0.51         ( v1_relat_1 @ C ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i]: ((k1_relat_1 @ (sk_C @ X5 @ X6)) = (X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.23/0.51  thf('5', plain, (![X8 : $i]: ((k1_relat_1 @ (sk_B_1 @ X8)) = (X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X10 : $i, X11 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X10)
% 0.23/0.51          | ~ (v1_funct_1 @ X10)
% 0.23/0.51          | ((X11) = (X10))
% 0.23/0.51          | ((k1_relat_1 @ X10) != (sk_A))
% 0.23/0.51          | ((k1_relat_1 @ X11) != (sk_A))
% 0.23/0.51          | ~ (v1_funct_1 @ X11)
% 0.23/0.51          | ~ (v1_relat_1 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((X0) != (sk_A))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (v1_funct_1 @ X1)
% 0.23/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.23/0.51          | ((X1) = (sk_B_1 @ X0))
% 0.23/0.51          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain, (![X8 : $i]: (v1_funct_1 @ (sk_B_1 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.23/0.51  thf('9', plain, (![X8 : $i]: (v1_relat_1 @ (sk_B_1 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((X0) != (sk_A))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (v1_funct_1 @ X1)
% 0.23/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.23/0.51          | ((X1) = (sk_B_1 @ X0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X1 : $i]:
% 0.23/0.51         (((X1) = (sk_B_1 @ sk_A))
% 0.23/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.23/0.51          | ~ (v1_funct_1 @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((X0) != (sk_A))
% 0.23/0.51          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.23/0.51          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.23/0.51          | ((sk_C @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['4', '11'])).
% 0.23/0.51  thf('13', plain, (![X5 : $i, X6 : $i]: (v1_relat_1 @ (sk_C @ X5 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.23/0.51  thf('14', plain, (![X5 : $i, X6 : $i]: (v1_funct_1 @ (sk_C @ X5 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((X0) != (sk_A)) | ((sk_C @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.51  thf('16', plain, (![X1 : $i]: ((sk_C @ X1 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.23/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.51         (((k1_funct_1 @ (sk_C @ X5 @ X6) @ X7) = (X5))
% 0.23/0.51          | ~ (r2_hidden @ X7 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((v1_xboole_0 @ X0)
% 0.23/0.51          | ((k1_funct_1 @ (sk_C @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_funct_1 @ (sk_B_1 @ sk_A) @ (sk_B @ sk_A)) = (X0))
% 0.23/0.51          | (v1_xboole_0 @ sk_A))),
% 0.23/0.51      inference('sup+', [status(thm)], ['16', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((np__1) = (X0)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.23/0.51      inference('sup+', [status(thm)], ['3', '20'])).
% 0.23/0.51  thf('22', plain, (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((np__1) = (X0)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.51  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.51  thf(t8_boole, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t8_boole])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.51  thf('26', plain, (![X0 : $i]: (((np__1) = (X0)) | ((k1_xboole_0) = (sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.23/0.51  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('28', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.23/0.51  thf('29', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.23/0.51  thf('30', plain, (((np__1) != (np__1))),
% 0.23/0.51      inference('demod', [status(thm)], ['0', '28', '29'])).
% 0.23/0.51  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
