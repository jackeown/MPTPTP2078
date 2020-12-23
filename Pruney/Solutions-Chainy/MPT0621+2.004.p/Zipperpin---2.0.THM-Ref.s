%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QljAFpkPa9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  384 ( 643 expanded)
%              Number of equality atoms :   49 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

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
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X16 ) )
      = X16 ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_relat_1 @ X18 )
       != sk_A )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('12',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_2 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X16 ) @ X17 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X12 ) @ ( sk_C @ X12 ) ) @ X12 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

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
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('35',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['3','35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QljAFpkPa9
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:58:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 88 iterations in 0.060s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(d2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (((X4) != (X3))
% 0.20/0.52          | (r2_hidden @ X4 @ X5)
% 0.20/0.52          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.20/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ?[C:$i]:
% 0.20/0.52       ( ( ![D:$i]:
% 0.20/0.52           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.52         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_C_1 @ X13 @ X14) @ X15) = (X13))
% 0.20/0.52          | ~ (r2_hidden @ X15 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X0)
% 0.20/0.52          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_1 @ X13 @ X14)) = (X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ?[B:$i]:
% 0.20/0.52       ( ( ![C:$i]:
% 0.20/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.52  thf('8', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B_2 @ X16)) = (X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf(t16_funct_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ![B:$i]:
% 0.20/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.52                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.52                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ![B:$i]:
% 0.20/0.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.52                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.52                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.52          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X18)
% 0.20/0.52          | ~ (v1_funct_1 @ X18)
% 0.20/0.52          | ((X19) = (X18))
% 0.20/0.52          | ((k1_relat_1 @ X18) != (sk_A))
% 0.20/0.52          | ((k1_relat_1 @ X19) != (sk_A))
% 0.20/0.52          | ~ (v1_funct_1 @ X19)
% 0.20/0.52          | ~ (v1_relat_1 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ((X1) = (sk_B_2 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B_2 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('12', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B_2 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ((X1) = (sk_B_2 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X1 : $i]:
% 0.20/0.52         (((X1) = (sk_B_2 @ sk_A))
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.52          | ((sk_C_1 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_1 @ X13 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_1 @ X13 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.52  thf('19', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B_2 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_B_2 @ X16) @ X17) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X17 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X0)
% 0.20/0.52          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (k1_xboole_0))
% 0.20/0.52          | (v1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '22'])).
% 0.20/0.52  thf(t56_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X12 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X12) @ (sk_C @ X12)) @ X12)
% 0.20/0.52          | ((X12) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0) | ((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf(cc1_relat_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.52  thf('27', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['23', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['6', '32'])).
% 0.20/0.52  thf('34', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('37', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '35', '36'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
