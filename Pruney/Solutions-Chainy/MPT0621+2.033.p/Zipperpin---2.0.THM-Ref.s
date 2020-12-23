%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kl09L67Iy4

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 139 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  399 (1375 expanded)
%              Number of equality atoms :   60 ( 202 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X12 @ X13 ) )
      = X13 ) ),
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

thf('1',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X15 ) )
      = X15 ) ),
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

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( ( k1_relat_1 @ X17 )
       != sk_A )
      | ( ( k1_relat_1 @ X18 )
       != sk_A )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( sk_B @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( sk_B @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X15 ) @ X16 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_funct_1 @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X12 @ X13 ) @ X14 )
        = X12 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C @ X2 @ X0 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kl09L67Iy4
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 76 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ?[C:$i]:
% 0.20/0.52       ( ( ![D:$i]:
% 0.20/0.52           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.52         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C @ X12 @ X13)) = (X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ?[B:$i]:
% 0.20/0.52       ( ( ![C:$i]:
% 0.20/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.52  thf('1', plain, (![X15 : $i]: ((k1_relat_1 @ (sk_B @ X15)) = (X15))),
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
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X17)
% 0.20/0.52          | ~ (v1_funct_1 @ X17)
% 0.20/0.52          | ((X18) = (X17))
% 0.20/0.52          | ((k1_relat_1 @ X17) != (sk_A))
% 0.20/0.52          | ((k1_relat_1 @ X18) != (sk_A))
% 0.20/0.52          | ~ (v1_funct_1 @ X18)
% 0.20/0.52          | ~ (v1_relat_1 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ((X1) = (sk_B @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, (![X15 : $i]: (v1_funct_1 @ (sk_B @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('5', plain, (![X15 : $i]: (v1_relat_1 @ (sk_B @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ((X1) = (sk_B @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X1 : $i]:
% 0.20/0.52         (((X1) = (sk_B @ sk_A))
% 0.20/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.20/0.52          | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.52  thf('9', plain, (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('10', plain, (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) != (sk_A)) | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('12', plain, (![X1 : $i]: ((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.52  thf(d5_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.52  thf(t152_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]: ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.52  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.52          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.52  thf(t4_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.52          | ((X1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_B @ X15) @ X16) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X16 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_D @ X0 @ X1 @ k1_xboole_0))
% 0.20/0.52              = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_C @ X0 @ sk_A) @ (sk_D @ sk_A @ X1 @ k1_xboole_0))
% 0.20/0.52            = (k1_xboole_0))
% 0.20/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['12', '22'])).
% 0.20/0.52  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k1_funct_1 @ (sk_C @ X0 @ sk_A) @ (sk_D @ sk_A @ X1 @ k1_xboole_0))
% 0.20/0.52           = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.52          | ((X1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (sk_C @ X12 @ X13) @ X14) = (X12))
% 0.20/0.52          | ~ (r2_hidden @ X14 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((k1_funct_1 @ (sk_C @ X2 @ X0) @ (sk_D @ X0 @ X1 @ k1_xboole_0))
% 0.20/0.52              = (X2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.52  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('35', plain, ($false),
% 0.20/0.52      inference('simplify_reflect+', [status(thm)], ['33', '34'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
