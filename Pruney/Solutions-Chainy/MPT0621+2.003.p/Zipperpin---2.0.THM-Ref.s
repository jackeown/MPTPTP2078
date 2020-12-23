%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mo7V1i4IYS

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  345 ( 502 expanded)
%              Number of equality atoms :   46 (  66 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(spc1_boole,axiom,(
    ~ ( v1_xboole_0 @ np__1 ) )).

thf('0',plain,(
    ~ ( v1_xboole_0 @ np__1 ) ),
    inference(cnf,[status(esa)],[spc1_boole])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X14 ) @ X15 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X14 ) )
      = X14 ) ),
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

thf('7',plain,(
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

thf('8',plain,(
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
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_2 @ X0 ) )
      | ( ( sk_B_2 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('15',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_B_2 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_B_2 @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X16 ) @ X17 )
        = np__1 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_funct_1 @ ( sk_B_1 @ sk_A ) @ ( sk_B @ sk_A ) )
      = np__1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0 = np__1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    k1_xboole_0 = np__1 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ np__1 ),
    inference(demod,[status(thm)],['1','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mo7V1i4IYS
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 79 iterations in 0.075s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.19/0.51  thf(np__1_type, type, np__1: $i).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(spc1_boole, axiom, (~( v1_xboole_0 @ np__1 ))).
% 0.19/0.51  thf('0', plain, (~ (v1_xboole_0 @ np__1)),
% 0.19/0.51      inference('cnf', [status(esa)], [spc1_boole])).
% 0.19/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.51  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.51  thf(d1_xboole_0, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ?[B:$i]:
% 0.19/0.51       ( ( ![C:$i]:
% 0.19/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.19/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (sk_B_1 @ X14) @ X15) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X15 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ?[B:$i]:
% 0.19/0.51       ( ( ![C:$i]:
% 0.19/0.51           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.19/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.51  thf('5', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B_2 @ X16)) = (X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.51  thf('6', plain, (![X14 : $i]: ((k1_relat_1 @ (sk_B_1 @ X14)) = (X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.51  thf(t16_funct_1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ![B:$i]:
% 0.19/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.51               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.51                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.51                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ![B:$i]:
% 0.19/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.51              ( ![C:$i]:
% 0.19/0.51                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.51                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.51                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.51                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.51          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X18)
% 0.19/0.51          | ~ (v1_funct_1 @ X18)
% 0.19/0.51          | ((X19) = (X18))
% 0.19/0.51          | ((k1_relat_1 @ X18) != (sk_A))
% 0.19/0.51          | ((k1_relat_1 @ X19) != (sk_A))
% 0.19/0.51          | ~ (v1_funct_1 @ X19)
% 0.19/0.51          | ~ (v1_relat_1 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X0) != (sk_A))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_funct_1 @ X1)
% 0.19/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.51          | ((X1) = (sk_B_1 @ X0))
% 0.19/0.51          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.19/0.51          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf('9', plain, (![X14 : $i]: (v1_funct_1 @ (sk_B_1 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.51  thf('10', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B_1 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X0) != (sk_A))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_funct_1 @ X1)
% 0.19/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.51          | ((X1) = (sk_B_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X1 : $i]:
% 0.19/0.51         (((X1) = (sk_B_1 @ sk_A))
% 0.19/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.51          | ~ (v1_funct_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((X0) != (sk_A))
% 0.19/0.51          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.19/0.51          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.19/0.51          | ((sk_B_2 @ X0) = (sk_B_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '12'])).
% 0.19/0.51  thf('14', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B_2 @ X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.51  thf('15', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B_2 @ X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i]: (((X0) != (sk_A)) | ((sk_B_2 @ X0) = (sk_B_1 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.51  thf('17', plain, (((sk_B_2 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (sk_B_2 @ X16) @ X17) = (np__1))
% 0.19/0.51          | ~ (r2_hidden @ X17 @ X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      ((((k1_funct_1 @ (sk_B_1 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.19/0.52        | (v1_xboole_0 @ sk_A))),
% 0.19/0.52      inference('sup+', [status(thm)], ['17', '20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((((k1_xboole_0) = (np__1)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.19/0.52      inference('sup+', [status(thm)], ['4', '21'])).
% 0.19/0.52  thf('23', plain, (((v1_xboole_0 @ sk_A) | ((k1_xboole_0) = (np__1)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.52  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.52  thf(t2_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.19/0.52       ( ( A ) = ( B ) ) ))).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X3 : $i, X4 : $i]:
% 0.19/0.52         (((X4) = (X3))
% 0.19/0.52          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.19/0.52          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.19/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.19/0.52          | ((X1) = (X0))
% 0.19/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '29'])).
% 0.19/0.52  thf('31', plain, ((((k1_xboole_0) = (np__1)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['23', '30'])).
% 0.19/0.52  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('33', plain, (((k1_xboole_0) = (np__1))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.19/0.52  thf('34', plain, ((v1_xboole_0 @ np__1)),
% 0.19/0.52      inference('demod', [status(thm)], ['1', '33'])).
% 0.19/0.52  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
