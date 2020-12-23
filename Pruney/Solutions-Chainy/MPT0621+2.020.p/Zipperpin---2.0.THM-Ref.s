%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2CIwrfxnD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  305 ( 494 expanded)
%              Number of equality atoms :   45 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X7 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X4 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X10 = X9 )
      | ( ( k1_relat_1 @ X9 )
       != sk_A )
      | ( ( k1_relat_1 @ X10 )
       != sk_A )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X7: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('9',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

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
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( sk_C @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_funct_1 @ ( sk_C @ X4 @ X5 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X4 @ X5 ) @ X6 )
        = X4 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
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
      ( ( k1_xboole_0 = X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2CIwrfxnD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 47 iterations in 0.037s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(t16_funct_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ![B:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.49                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.21/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ![B:$i]:
% 0.21/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.49                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.21/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.21/0.49  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ?[B:$i]:
% 0.21/0.49       ( ( ![C:$i]:
% 0.21/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (sk_B_1 @ X7) @ X8) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X8 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ?[C:$i]:
% 0.21/0.49       ( ( ![D:$i]:
% 0.21/0.49           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.21/0.49         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]: ((k1_relat_1 @ (sk_C @ X4 @ X5)) = (X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.49  thf('5', plain, (![X7 : $i]: ((k1_relat_1 @ (sk_B_1 @ X7)) = (X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ((X10) = (X9))
% 0.21/0.49          | ((k1_relat_1 @ X9) != (sk_A))
% 0.21/0.49          | ((k1_relat_1 @ X10) != (sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (sk_A))
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X1)
% 0.21/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.49          | ((X1) = (sk_B_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, (![X7 : $i]: (v1_funct_1 @ (sk_B_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('9', plain, (![X7 : $i]: (v1_relat_1 @ (sk_B_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (sk_A))
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X1)
% 0.21/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.49          | ((X1) = (sk_B_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (((X1) = (sk_B_1 @ sk_A))
% 0.21/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (sk_A))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.21/0.49          | ((sk_C @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.49  thf('13', plain, (![X4 : $i, X5 : $i]: (v1_relat_1 @ (sk_C @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.49  thf('14', plain, (![X4 : $i, X5 : $i]: (v1_funct_1 @ (sk_C @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (sk_A)) | ((sk_C @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.49  thf('16', plain, (![X1 : $i]: ((sk_C @ X1 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (sk_C @ X4 @ X5) @ X6) = (X4))
% 0.21/0.49          | ~ (r2_hidden @ X6 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | ((k1_funct_1 @ (sk_C @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (sk_B_1 @ sk_A) @ (sk_B @ sk_A)) = (X0))
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['16', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) = (X0)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((k1_xboole_0) = (X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.49  thf(l13_xboole_0, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.49  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
