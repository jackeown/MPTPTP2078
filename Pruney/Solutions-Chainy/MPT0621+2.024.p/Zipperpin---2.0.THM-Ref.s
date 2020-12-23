%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K94wgladCq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 ( 498 expanded)
%              Number of equality atoms :   50 (  79 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
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

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X3 ) @ X4 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X3 ) )
      = X3 ) ),
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

thf('6',plain,(
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
    ! [X3: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('9',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X3 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_2 @ X0 ) )
      | ( ( sk_B_2 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('14',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_B_2 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( sk_B_2 @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X5 ) @ X6 )
        = np__1 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_funct_1 @ ( sk_B_1 @ sk_A ) @ ( sk_B @ sk_A ) )
      = np__1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_funct_1 @ ( sk_B_1 @ sk_A ) @ ( sk_B @ sk_A ) )
    = np__1 ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    k1_xboole_0 = np__1 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = np__1 ) ),
    inference(demod,[status(thm)],['0','25'])).

thf(spc1_boole,axiom,(
    ~ ( v1_xboole_0 @ np__1 ) )).

thf('27',plain,(
    ~ ( v1_xboole_0 @ np__1 ) ),
    inference(cnf,[status(esa)],[spc1_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('29',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K94wgladCq
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:16:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 45 iterations in 0.017s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.19/0.46  thf(np__1_type, type, np__1: $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.46  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('0', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.46  thf(t7_xboole_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.46  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ?[B:$i]:
% 0.19/0.46       ( ( ![C:$i]:
% 0.19/0.46           ( ( r2_hidden @ C @ A ) =>
% 0.19/0.46             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.46         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.46         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (((k1_funct_1 @ (sk_B_1 @ X3) @ X4) = (k1_xboole_0))
% 0.19/0.46          | ~ (r2_hidden @ X4 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0))
% 0.19/0.46          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ?[B:$i]:
% 0.19/0.46       ( ( ![C:$i]:
% 0.19/0.46           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.19/0.46         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.46         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.46  thf('4', plain, (![X5 : $i]: ((k1_relat_1 @ (sk_B_2 @ X5)) = (X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.46  thf('5', plain, (![X3 : $i]: ((k1_relat_1 @ (sk_B_1 @ X3)) = (X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf(t16_funct_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ![B:$i]:
% 0.19/0.46         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.46                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.46                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.46       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ![B:$i]:
% 0.19/0.46            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46              ( ![C:$i]:
% 0.19/0.46                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.46                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.46                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.46          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X7)
% 0.19/0.46          | ~ (v1_funct_1 @ X7)
% 0.19/0.46          | ((X8) = (X7))
% 0.19/0.46          | ((k1_relat_1 @ X7) != (sk_A))
% 0.19/0.46          | ((k1_relat_1 @ X8) != (sk_A))
% 0.19/0.46          | ~ (v1_funct_1 @ X8)
% 0.19/0.46          | ~ (v1_relat_1 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((X0) != (sk_A))
% 0.19/0.46          | ~ (v1_relat_1 @ X1)
% 0.19/0.46          | ~ (v1_funct_1 @ X1)
% 0.19/0.46          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.46          | ((X1) = (sk_B_1 @ X0))
% 0.19/0.46          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain, (![X3 : $i]: (v1_funct_1 @ (sk_B_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('9', plain, (![X3 : $i]: (v1_relat_1 @ (sk_B_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((X0) != (sk_A))
% 0.19/0.46          | ~ (v1_relat_1 @ X1)
% 0.19/0.46          | ~ (v1_funct_1 @ X1)
% 0.19/0.46          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.46          | ((X1) = (sk_B_1 @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X1 : $i]:
% 0.19/0.46         (((X1) = (sk_B_1 @ sk_A))
% 0.19/0.46          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.46          | ~ (v1_funct_1 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X1))),
% 0.19/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) != (sk_A))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.19/0.46          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.19/0.46          | ((sk_B_2 @ X0) = (sk_B_1 @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '11'])).
% 0.19/0.46  thf('13', plain, (![X5 : $i]: (v1_relat_1 @ (sk_B_2 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.46  thf('14', plain, (![X5 : $i]: (v1_funct_1 @ (sk_B_2 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) != (sk_A)) | ((sk_B_2 @ X0) = (sk_B_1 @ sk_A)))),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.19/0.46  thf('16', plain, (((sk_B_2 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.19/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (((k1_funct_1 @ (sk_B_2 @ X5) @ X6) = (np__1))
% 0.19/0.46          | ~ (r2_hidden @ X6 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0))
% 0.19/0.46          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((((k1_funct_1 @ (sk_B_1 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.19/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['16', '19'])).
% 0.19/0.46  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (((k1_funct_1 @ (sk_B_1 @ sk_A) @ (sk_B @ sk_A)) = (np__1))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf('23', plain, ((((k1_xboole_0) = (np__1)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '22'])).
% 0.19/0.46  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('25', plain, (((k1_xboole_0) = (np__1))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.19/0.46  thf('26', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (np__1))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '25'])).
% 0.19/0.46  thf(spc1_boole, axiom, (~( v1_xboole_0 @ np__1 ))).
% 0.19/0.46  thf('27', plain, (~ (v1_xboole_0 @ np__1)),
% 0.19/0.46      inference('cnf', [status(esa)], [spc1_boole])).
% 0.19/0.46  thf('28', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.19/0.46  thf('29', plain, (![X2 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.19/0.46  thf('30', plain, ($false), inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
