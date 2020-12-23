%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f5JFkZ340g

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 126 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  363 (1243 expanded)
%              Number of equality atoms :   57 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X7 @ X8 ) )
      = X8 ) ),
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
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X10 ) )
      = X10 ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_relat_1 @ X12 )
       != sk_A )
      | ( ( k1_relat_1 @ X13 )
       != sk_A )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X10: $i] :
      ( v1_funct_1 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( sk_B @ X10 ) ) ),
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
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X10 ) @ X11 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0 = sk_A ) ) ),
    inference('sup+',[status(thm)],['12','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X7 @ X8 ) @ X9 )
        = X7 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f5JFkZ340g
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 57 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ?[C:$i]:
% 0.20/0.48       ( ( ![D:$i]:
% 0.20/0.48           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]: ((k1_relat_1 @ (sk_C_1 @ X7 @ X8)) = (X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ?[B:$i]:
% 0.20/0.48       ( ( ![C:$i]:
% 0.20/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('1', plain, (![X10 : $i]: ((k1_relat_1 @ (sk_B @ X10)) = (X10))),
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
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X12)
% 0.20/0.48          | ((X13) = (X12))
% 0.20/0.48          | ((k1_relat_1 @ X12) != (sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X13) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (v1_relat_1 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, (![X10 : $i]: (v1_funct_1 @ (sk_B @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('5', plain, (![X10 : $i]: (v1_relat_1 @ (sk_B @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (((X1) = (sk_B @ sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.48          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.48  thf('9', plain, (![X7 : $i, X8 : $i]: (v1_relat_1 @ (sk_C_1 @ X7 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('10', plain, (![X7 : $i, X8 : $i]: (v1_funct_1 @ (sk_C_1 @ X7 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.48  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.48  thf(t2_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.48       ( ( A ) = ( B ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X1) = (X0))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_tarski])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf(t152_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.48  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_B @ X10) @ X11) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X11 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (X0))
% 0.20/0.48          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.20/0.48              = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.20/0.48            = (k1_xboole_0))
% 0.20/0.48          | ((k1_xboole_0) = (sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '20'])).
% 0.20/0.48  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.20/0.48           = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_C_1 @ X7 @ X8) @ X9) = (X7))
% 0.20/0.48          | ~ (r2_hidden @ X9 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (X0))
% 0.20/0.48          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.20/0.48              = (X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((k1_xboole_0) = (sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.48  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('33', plain, ($false),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
