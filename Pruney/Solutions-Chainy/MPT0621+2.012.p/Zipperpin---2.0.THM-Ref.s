%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bkQJUeEXMK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 127 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  363 (1243 expanded)
%              Number of equality atoms :   56 ( 186 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

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
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
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
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X10 @ ( k1_tarski @ X9 ) )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X15 ) @ X16 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0 = sk_A ) ) ),
    inference('sup+',[status(thm)],['12','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) @ X14 )
        = X12 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( k1_xboole_0 = sk_A ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bkQJUeEXMK
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:16:45 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 152 iterations in 0.090s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.55  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ?[C:$i]:
% 0.22/0.55       ( ( ![D:$i]:
% 0.22/0.55           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.22/0.55         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.55         ( v1_relat_1 @ C ) ) ))).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.55  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ?[B:$i]:
% 0.22/0.55       ( ( ![C:$i]:
% 0.22/0.55           ( ( r2_hidden @ C @ A ) =>
% 0.22/0.55             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.55         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.22/0.55         ( v1_relat_1 @ B ) ) ))).
% 0.22/0.55  thf('1', plain, (![X15 : $i]: ((k1_relat_1 @ (sk_B @ X15)) = (X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.55  thf(t16_funct_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.55               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.55                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.55                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.55       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ![B:$i]:
% 0.22/0.55            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.55                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.55                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.55                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.55          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X17)
% 0.22/0.55          | ~ (v1_funct_1 @ X17)
% 0.22/0.55          | ((X18) = (X17))
% 0.22/0.55          | ((k1_relat_1 @ X17) != (sk_A))
% 0.22/0.55          | ((k1_relat_1 @ X18) != (sk_A))
% 0.22/0.55          | ~ (v1_funct_1 @ X18)
% 0.22/0.55          | ~ (v1_relat_1 @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((X0) != (sk_A))
% 0.22/0.55          | ~ (v1_relat_1 @ X1)
% 0.22/0.55          | ~ (v1_funct_1 @ X1)
% 0.22/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.55          | ((X1) = (sk_B @ X0))
% 0.22/0.55          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain, (![X15 : $i]: (v1_funct_1 @ (sk_B @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.55  thf('5', plain, (![X15 : $i]: (v1_relat_1 @ (sk_B @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((X0) != (sk_A))
% 0.22/0.55          | ~ (v1_relat_1 @ X1)
% 0.22/0.55          | ~ (v1_funct_1 @ X1)
% 0.22/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.55          | ((X1) = (sk_B @ X0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X1 : $i]:
% 0.22/0.55         (((X1) = (sk_B @ sk_A))
% 0.22/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.55          | ~ (v1_funct_1 @ X1)
% 0.22/0.55          | ~ (v1_relat_1 @ X1))),
% 0.22/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((X0) != (sk_A))
% 0.22/0.55          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.22/0.55          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 0.22/0.55          | ((sk_C_2 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.55  thf('9', plain, (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((X0) != (sk_A)) | ((sk_C_2 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.22/0.55  thf('12', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.22/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.55  thf(t2_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.55       ( ( A ) = ( B ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((X1) = (X0))
% 0.22/0.55          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.55          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.55  thf(t4_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.55  thf(t65_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.55          | ((k4_xboole_0 @ X10 @ (k1_tarski @ X9)) != (X10)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i]:
% 0.22/0.55         (((k1_funct_1 @ (sk_B @ X15) @ X16) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X16 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_xboole_0) = (X0))
% 0.22/0.55          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.22/0.55              = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_funct_1 @ (sk_C_2 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.22/0.55            = (k1_xboole_0))
% 0.22/0.55          | ((k1_xboole_0) = (sk_A)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['12', '20'])).
% 0.22/0.55  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k1_funct_1 @ (sk_C_2 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.22/0.55           = (k1_xboole_0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         (((k1_funct_1 @ (sk_C_2 @ X12 @ X13) @ X14) = (X12))
% 0.22/0.55          | ~ (r2_hidden @ X14 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k1_xboole_0) = (X0))
% 0.22/0.55          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.22/0.55              = (X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((k1_xboole_0) = (sk_A)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.55  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('33', plain, ($false),
% 0.22/0.55      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
