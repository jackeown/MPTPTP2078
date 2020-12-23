%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O54Z8zGphG

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 141 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  392 (1359 expanded)
%              Number of equality atoms :   61 ( 206 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X20: $i,X21: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X20 @ X21 ) )
      = X21 ) ),
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
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X26 = X25 )
      | ( ( k1_relat_1 @ X25 )
       != sk_A )
      | ( ( k1_relat_1 @ X26 )
       != sk_A )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X20 @ X21 ) ) ),
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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X15 ) @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X23 ) @ X24 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X20 @ X21 ) @ X22 )
        = X20 )
      | ~ ( r2_hidden @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O54Z8zGphG
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:37:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 76 iterations in 0.045s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ?[C:$i]:
% 0.19/0.50       ( ( ![D:$i]:
% 0.19/0.50           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.19/0.50         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.50         ( v1_relat_1 @ C ) ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]: ((k1_relat_1 @ (sk_C_1 @ X20 @ X21)) = (X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ?[B:$i]:
% 0.19/0.50       ( ( ![C:$i]:
% 0.19/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.19/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.50  thf('1', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf(t16_funct_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ![B:$i]:
% 0.19/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.50                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ![B:$i]:
% 0.19/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.50                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.50          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X25)
% 0.19/0.50          | ~ (v1_funct_1 @ X25)
% 0.19/0.50          | ((X26) = (X25))
% 0.19/0.50          | ((k1_relat_1 @ X25) != (sk_A))
% 0.19/0.50          | ((k1_relat_1 @ X26) != (sk_A))
% 0.19/0.50          | ~ (v1_funct_1 @ X26)
% 0.19/0.50          | ~ (v1_relat_1 @ X26))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ((X1) = (sk_B @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('5', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ((X1) = (sk_B @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X1 : $i]:
% 0.19/0.50         (((X1) = (sk_B @ sk_A))
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_relat_1 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.50          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.50  thf('9', plain, (![X20 : $i, X21 : $i]: (v1_relat_1 @ (sk_C_1 @ X20 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]: (v1_funct_1 @ (sk_C_1 @ X20 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.50  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.19/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.50  thf(d5_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.50       ( ![C:$i]:
% 0.19/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X15 : $i, X18 : $i]:
% 0.19/0.50         (((X18) = (k2_relat_1 @ X15))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ (sk_D_1 @ X18 @ X15) @ (sk_C @ X18 @ X15)) @ X15)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.50  thf(t113_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.50  thf(t152_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.19/0.50  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.50          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.50  thf(t60_relat_1, axiom,
% 0.19/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('19', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_B @ X23) @ X24) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X24 @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.19/0.50              = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['12', '22'])).
% 0.19/0.50  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.19/0.50           = (k1_xboole_0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X20 @ X21) @ X22) = (X20))
% 0.19/0.50          | ~ (r2_hidden @ X22 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.19/0.50              = (X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['25', '28'])).
% 0.19/0.50  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('35', plain, ($false),
% 0.19/0.50      inference('simplify_reflect+', [status(thm)], ['33', '34'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
