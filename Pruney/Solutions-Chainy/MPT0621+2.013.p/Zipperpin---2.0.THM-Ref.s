%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F9Iwf2mO8h

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 131 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   23
%              Number of atoms          :  477 (1739 expanded)
%              Number of equality atoms :   78 ( 300 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( sk_C_1 @ X5 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( sk_C_1 @ X5 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_1 @ X5 @ X6 ) )
        = X6 )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( sk_C_1 @ X5 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( sk_C_1 @ X5 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_1 @ X5 @ X6 ) )
        = X6 )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

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

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k1_relat_1 @ X7 )
       != sk_A )
      | ( ( k1_relat_1 @ X8 )
       != sk_A )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ( X2
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ( X2
        = ( sk_C_1 @ X1 @ sk_A ) )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ( X2
        = ( sk_C_1 @ X1 @ sk_A ) )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X1
        = ( sk_C_1 @ X0 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_C_1 @ X0 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_C_1 @ X2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X1 @ sk_A )
        = ( sk_C_1 @ X2 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X1 @ sk_A )
        = ( sk_C_1 @ X2 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = ( sk_C_1 @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = ( sk_C_1 @ X1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = ( sk_C_1 @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1 @ X0 @ sk_A )
      = ( sk_C_1 @ X1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_1 @ X5 @ X6 ) )
        = ( k1_tarski @ X5 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_1 @ X0 @ sk_A ) )
        = ( k1_tarski @ X1 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('36',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F9Iwf2mO8h
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 52 iterations in 0.026s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(d1_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.49  thf(t15_funct_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ?[C:$i]:
% 0.22/0.49           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.22/0.49             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.49             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((v1_relat_1 @ (sk_C_1 @ X5 @ X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((v1_funct_1 @ (sk_C_1 @ X5 @ X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (sk_C_1 @ X5 @ X6)) = (X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((v1_funct_1 @ (sk_C_1 @ X5 @ X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((v1_relat_1 @ (sk_C_1 @ X5 @ X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (sk_C_1 @ X5 @ X6)) = (X6)) | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf(t16_funct_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ![B:$i]:
% 0.22/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.49               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.49                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.49                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ![B:$i]:
% 0.22/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.49              ( ![C:$i]:
% 0.22/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.49                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.49                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.49                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X7)
% 0.22/0.49          | ~ (v1_funct_1 @ X7)
% 0.22/0.49          | ((X8) = (X7))
% 0.22/0.49          | ((k1_relat_1 @ X7) != (sk_A))
% 0.22/0.49          | ((k1_relat_1 @ X8) != (sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ X8)
% 0.22/0.49          | ~ (v1_relat_1 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((X0) != (sk_A))
% 0.22/0.49          | ((X0) = (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ X2)
% 0.22/0.49          | ~ (v1_funct_1 @ X2)
% 0.22/0.49          | ((k1_relat_1 @ X2) != (sk_A))
% 0.22/0.49          | ((X2) = (sk_C_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ((X2) = (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ((k1_relat_1 @ X2) != (sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ X2)
% 0.22/0.49          | ~ (v1_relat_1 @ X2)
% 0.22/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ((X2) = (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ((k1_relat_1 @ X2) != (sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ X2)
% 0.22/0.49          | ~ (v1_relat_1 @ X2))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((sk_A) = (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.49          | ((X1) = (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.49  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.49          | ((X1) = (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ sk_A)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((sk_A) = (k1_xboole_0))
% 0.22/0.49          | ((X1) = (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '15'])).
% 0.22/0.49  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((X1) = (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((X0) != (sk_A))
% 0.22/0.49          | ((X0) = (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.22/0.49          | ((sk_C_1 @ X1 @ X0) = (sk_C_1 @ X2 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         (((sk_C_1 @ X1 @ sk_A) = (sk_C_1 @ X2 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         (((sk_C_1 @ X1 @ sk_A) = (sk_C_1 @ X2 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ sk_A))
% 0.22/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ sk_A)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((sk_A) = (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ((sk_C_1 @ X0 @ sk_A) = (sk_C_1 @ X1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '22'])).
% 0.22/0.49  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (sk_C_1 @ X0 @ sk_A))
% 0.22/0.49          | ((sk_C_1 @ X0 @ sk_A) = (sk_C_1 @ X1 @ sk_A)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((sk_A) = (k1_xboole_0))
% 0.22/0.49          | ((sk_C_1 @ X0 @ sk_A) = (sk_C_1 @ X1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '25'])).
% 0.22/0.49  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((sk_C_1 @ X0 @ sk_A) = (sk_C_1 @ X1 @ sk_A))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((k2_relat_1 @ (sk_C_1 @ X5 @ X6)) = (k1_tarski @ X5))
% 0.22/0.49          | ((X6) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k2_relat_1 @ (sk_C_1 @ X0 @ sk_A)) = (k1_tarski @ X1))
% 0.22/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_relat_1 @ (sk_C_1 @ X0 @ sk_A)) = (k1_tarski @ X1))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_relat_1 @ (sk_C_1 @ X0 @ sk_A)) = (k1_tarski @ X1))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k1_tarski @ X0) = (k1_tarski @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X0 : $i, X3 : $i]:
% 0.22/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k1_tarski @ X0)) | ((X2) = (X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '36'])).
% 0.22/0.49  thf('38', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '37'])).
% 0.22/0.49  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
