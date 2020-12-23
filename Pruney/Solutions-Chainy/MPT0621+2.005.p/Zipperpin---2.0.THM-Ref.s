%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1FcBwAxD9U

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 ( 483 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(np__1_type,type,(
    np__1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_4_type,type,(
    sk_B_4: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    ! [X83: $i,X84: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_3 @ X83 ) @ X84 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X84 @ X83 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_3 @ X0 ) @ ( sk_B_1 @ X0 ) )
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
    ! [X85: $i] :
      ( ( k1_relat_1 @ ( sk_B_4 @ X85 ) )
      = X85 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X83: $i] :
      ( ( k1_relat_1 @ ( sk_B_3 @ X83 ) )
      = X83 ) ),
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
    ! [X87: $i,X88: $i] :
      ( ~ ( v1_relat_1 @ X87 )
      | ~ ( v1_funct_1 @ X87 )
      | ( X88 = X87 )
      | ( ( k1_relat_1 @ X87 )
       != sk_A )
      | ( ( k1_relat_1 @ X88 )
       != sk_A )
      | ~ ( v1_funct_1 @ X88 )
      | ~ ( v1_relat_1 @ X88 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_3 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_3 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X83: $i] :
      ( v1_funct_1 @ ( sk_B_3 @ X83 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('10',plain,(
    ! [X83: $i] :
      ( v1_relat_1 @ ( sk_B_3 @ X83 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_3 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_B_4 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_4 @ X0 ) )
      | ( ( sk_B_4 @ X0 )
        = ( sk_B_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X85: $i] :
      ( v1_relat_1 @ ( sk_B_4 @ X85 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('15',plain,(
    ! [X85: $i] :
      ( v1_funct_1 @ ( sk_B_4 @ X85 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_B_4 @ X0 )
        = ( sk_B_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_B_4 @ sk_A )
    = ( sk_B_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X85: $i,X86: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_4 @ X85 ) @ X86 )
        = np__1 )
      | ~ ( r2_hidden @ X86 @ X85 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_4 @ X0 ) @ ( sk_B_1 @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_funct_1 @ ( sk_B_3 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
      = np__1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_funct_1 @ ( sk_B_3 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    = np__1 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    k1_xboole_0 = np__1 ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ np__1 ),
    inference(demod,[status(thm)],['1','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1FcBwAxD9U
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 116 iterations in 0.065s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(np__1_type, type, np__1: $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_B_4_type, type, sk_B_4: $i > $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(spc1_boole, axiom, (~( v1_xboole_0 @ np__1 ))).
% 0.20/0.53  thf('0', plain, (~ (v1_xboole_0 @ np__1)),
% 0.20/0.53      inference('cnf', [status(esa)], [spc1_boole])).
% 0.20/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.53  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X10 : $i]:
% 0.20/0.53         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X10) @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ?[B:$i]:
% 0.20/0.53       ( ( ![C:$i]:
% 0.20/0.53           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.53             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.53         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.53         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X83 : $i, X84 : $i]:
% 0.20/0.53         (((k1_funct_1 @ (sk_B_3 @ X83) @ X84) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X84 @ X83))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ((k1_funct_1 @ (sk_B_3 @ X0) @ (sk_B_1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ?[B:$i]:
% 0.20/0.53       ( ( ![C:$i]:
% 0.20/0.53           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.20/0.53         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.53         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.53  thf('5', plain, (![X85 : $i]: ((k1_relat_1 @ (sk_B_4 @ X85)) = (X85))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.53  thf('6', plain, (![X83 : $i]: ((k1_relat_1 @ (sk_B_3 @ X83)) = (X83))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.53  thf(t16_funct_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ![B:$i]:
% 0.20/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.53                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.53                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.53       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ![B:$i]:
% 0.20/0.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.53                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.53                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.53          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X87 : $i, X88 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X87)
% 0.20/0.53          | ~ (v1_funct_1 @ X87)
% 0.20/0.53          | ((X88) = (X87))
% 0.20/0.53          | ((k1_relat_1 @ X87) != (sk_A))
% 0.20/0.53          | ((k1_relat_1 @ X88) != (sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ X88)
% 0.20/0.53          | ~ (v1_relat_1 @ X88))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) != (sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.53          | ((X1) = (sk_B_3 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ (sk_B_3 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ (sk_B_3 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, (![X83 : $i]: (v1_funct_1 @ (sk_B_3 @ X83))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.53  thf('10', plain, (![X83 : $i]: (v1_relat_1 @ (sk_B_3 @ X83))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) != (sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.53          | ((X1) = (sk_B_3 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         (((X1) = (sk_B_3 @ sk_A))
% 0.20/0.53          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) != (sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ (sk_B_4 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ (sk_B_4 @ X0))
% 0.20/0.53          | ((sk_B_4 @ X0) = (sk_B_3 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '12'])).
% 0.20/0.53  thf('14', plain, (![X85 : $i]: (v1_relat_1 @ (sk_B_4 @ X85))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.53  thf('15', plain, (![X85 : $i]: (v1_funct_1 @ (sk_B_4 @ X85))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]: (((X0) != (sk_A)) | ((sk_B_4 @ X0) = (sk_B_3 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.53  thf('17', plain, (((sk_B_4 @ sk_A) = (sk_B_3 @ sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X10 : $i]:
% 0.20/0.53         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X10) @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X85 : $i, X86 : $i]:
% 0.20/0.53         (((k1_funct_1 @ (sk_B_4 @ X85) @ X86) = (np__1))
% 0.20/0.53          | ~ (r2_hidden @ X86 @ X85))),
% 0.20/0.53      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ((k1_funct_1 @ (sk_B_4 @ X0) @ (sk_B_1 @ X0)) = (np__1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((k1_funct_1 @ (sk_B_3 @ sk_A) @ (sk_B_1 @ sk_A)) = (np__1))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.53  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((k1_funct_1 @ (sk_B_3 @ sk_A) @ (sk_B_1 @ sk_A)) = (np__1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain, ((((k1_xboole_0) = (np__1)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '23'])).
% 0.20/0.53  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, (((k1_xboole_0) = (np__1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, ((v1_xboole_0 @ np__1)),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '26'])).
% 0.20/0.53  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
