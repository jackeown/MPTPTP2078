%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cK7vhvhpDb

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 157 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 (1359 expanded)
%              Number of equality atoms :   53 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X19 @ X20 ) @ X21 )
        = X19 )
      | ~ ( r2_hidden @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X19 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

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

thf('5',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X25 = X24 )
      | ( ( k1_relat_1 @ X24 )
       != sk_A )
      | ( ( k1_relat_1 @ X25 )
       != sk_A )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('9',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X22 ) ) ),
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
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X22 ) @ X23 )
        = np__1 )
      | ~ ( r2_hidden @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = np__1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
      = np__1 ) ),
    inference(clc,[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = np__1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('35',plain,(
    ! [X0: $i] : ( X0 = np__1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] : ( X0 = np__1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('37',plain,(
    np__1 != np__1 ),
    inference(demod,[status(thm)],['0','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cK7vhvhpDb
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 209 iterations in 0.097s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.56  thf(np__1_type, type, np__1: $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(t16_funct_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ![B:$i]:
% 0.38/0.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.56                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.56                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.38/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ![B:$i]:
% 0.38/0.56            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.56                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.56                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.38/0.56          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.38/0.56  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ?[C:$i]:
% 0.38/0.56       ( ( ![D:$i]:
% 0.38/0.56           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.38/0.56         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.38/0.56         ( v1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.56         (((k1_funct_1 @ (sk_C_2 @ X19 @ X20) @ X21) = (X19))
% 0.38/0.56          | ~ (r2_hidden @ X21 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i]: ((k1_relat_1 @ (sk_C_2 @ X19 @ X20)) = (X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.56  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ?[B:$i]:
% 0.38/0.56       ( ( ![C:$i]:
% 0.38/0.56           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.38/0.56         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.38/0.56         ( v1_relat_1 @ B ) ) ))).
% 0.38/0.56  thf('5', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B_1 @ X22)) = (X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X24)
% 0.38/0.56          | ~ (v1_funct_1 @ X24)
% 0.38/0.56          | ((X25) = (X24))
% 0.38/0.56          | ((k1_relat_1 @ X24) != (sk_A))
% 0.38/0.56          | ((k1_relat_1 @ X25) != (sk_A))
% 0.38/0.56          | ~ (v1_funct_1 @ X25)
% 0.38/0.56          | ~ (v1_relat_1 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (sk_A))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.56          | ((X1) = (sk_B_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B_1 @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.38/0.56  thf('9', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B_1 @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (sk_A))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.56          | ((X1) = (sk_B_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (((X1) = (sk_B_1 @ sk_A))
% 0.38/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (sk_A))
% 0.38/0.56          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 0.38/0.56          | ((sk_C_2 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (sk_C_2 @ X19 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i]: (v1_funct_1 @ (sk_C_2 @ X19 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (sk_A)) | ((sk_C_2 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.56  thf('16', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.38/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X22 : $i, X23 : $i]:
% 0.38/0.56         (((k1_funct_1 @ (sk_B_1 @ X22) @ X23) = (np__1))
% 0.38/0.56          | ~ (r2_hidden @ X23 @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_funct_1 @ (sk_C_2 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.38/0.56          | (v1_xboole_0 @ sk_A))),
% 0.38/0.56      inference('sup+', [status(thm)], ['16', '19'])).
% 0.38/0.56  thf(t2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.38/0.56       ( ( A ) = ( B ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]:
% 0.38/0.56         (((X4) = (X3))
% 0.38/0.56          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.38/0.56          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_tarski])).
% 0.38/0.56  thf(t113_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.56  thf(t152_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.38/0.56  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '25'])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('30', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k1_funct_1 @ (sk_C_2 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (np__1))),
% 0.38/0.56      inference('clc', [status(thm)], ['20', '31'])).
% 0.38/0.56  thf('33', plain, (![X0 : $i]: (((X0) = (np__1)) | (v1_xboole_0 @ sk_A))),
% 0.38/0.56      inference('sup+', [status(thm)], ['3', '32'])).
% 0.38/0.56  thf('34', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.56  thf('35', plain, (![X0 : $i]: ((X0) = (np__1))),
% 0.38/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain, (![X0 : $i]: ((X0) = (np__1))),
% 0.38/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('37', plain, (((np__1) != (np__1))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '35', '36'])).
% 0.38/0.56  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.42/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
