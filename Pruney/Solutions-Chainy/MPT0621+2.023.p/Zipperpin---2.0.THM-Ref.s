%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S95oDLz2p7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 115 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  422 (1295 expanded)
%              Number of equality atoms :   71 ( 222 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X11 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X11 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X11 @ X12 ) )
        = X12 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

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

thf('8',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_relat_1 @ X13 )
       != sk_A )
      | ( ( k1_relat_1 @ X14 )
       != sk_A )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('12',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ X1 @ sk_A )
        = ( sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ X1 @ sk_A )
        = ( sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ sk_A ) )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X0 @ sk_A ) )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X11 @ X12 ) )
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('33',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference(demod,[status(thm)],['4','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S95oDLz2p7
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 32 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('0', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(d2_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.48          | ((X4) = (X3))
% 0.20/0.48          | ((X4) = (X0))
% 0.20/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (((X4) = (X0))
% 0.20/0.48          | ((X4) = (X3))
% 0.20/0.48          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf(t15_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ?[C:$i]:
% 0.20/0.48           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.48             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((v1_relat_1 @ (sk_C @ X11 @ X12)) | ((X12) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((v1_funct_1 @ (sk_C @ X11 @ X12)) | ((X12) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (sk_C @ X11 @ X12)) = (X12)) | ((X12) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ?[B:$i]:
% 0.20/0.48       ( ( ![C:$i]:
% 0.20/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('8', plain, (![X9 : $i]: ((k1_relat_1 @ (sk_B @ X9)) = (X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t16_funct_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ![B:$i]:
% 0.20/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ![B:$i]:
% 0.20/0.48            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.48                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.48          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X13)
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ((X14) = (X13))
% 0.20/0.48          | ((k1_relat_1 @ X13) != (sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X14) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X14)
% 0.20/0.48          | ~ (v1_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, (![X9 : $i]: (v1_funct_1 @ (sk_B @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('12', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (((X1) = (sk_B @ sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.20/0.48          | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X1 @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X0 @ sk_A))
% 0.20/0.48          | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '18'])).
% 0.20/0.48  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ (sk_C @ X0 @ sk_A))
% 0.20/0.48          | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (k1_xboole_0)) | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '21'])).
% 0.20/0.48  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (sk_C @ X11 @ X12)) = (k1_tarski @ X11))
% 0.20/0.48          | ((X12) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))
% 0.20/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]: ((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]: ((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k1_tarski @ X0) = (k1_tarski @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X1) != (X0))
% 0.20/0.48          | (r2_hidden @ X1 @ X2)
% 0.20/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['31', '33'])).
% 0.20/0.48  thf('35', plain, (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['30', '34'])).
% 0.20/0.48  thf('36', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '35'])).
% 0.20/0.48  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
