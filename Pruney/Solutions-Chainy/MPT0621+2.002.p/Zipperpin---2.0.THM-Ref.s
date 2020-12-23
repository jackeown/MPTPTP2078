%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CW6tmCt2TE

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
% Statistics : Number of formulae       :   66 ( 261 expanded)
%              Number of leaves         :   20 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  485 (2671 expanded)
%              Number of equality atoms :   65 ( 338 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('1',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ( X1
        = ( k2_relat_1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('5',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( X1
        = ( k2_relat_1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( X1
        = ( k2_relat_1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = np__1 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ ( sk_B @ k1_xboole_0 ) ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ( ( k1_relat_1 @ X20 )
       != sk_A )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ ( sk_B @ k1_xboole_0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ ( sk_B @ k1_xboole_0 ) ) )
        = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ ( sk_B @ k1_xboole_0 ) ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('43',plain,(
    np__1 != np__1 ),
    inference(demod,[status(thm)],['0','41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CW6tmCt2TE
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 59 iterations in 0.046s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(np__1_type, type, np__1: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(t16_funct_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ![B:$i]:
% 0.20/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.50          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.50  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( ![C:$i]:
% 0.20/0.50           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('1', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf(d5_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.50               ( ?[D:$i]:
% 0.20/0.50                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.50                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.20/0.50          | ((X7) = (k2_relat_1 @ X8))
% 0.20/0.50          | ~ (v1_funct_1 @ X8)
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ (sk_B @ X0)) @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.50          | ((X1) = (k2_relat_1 @ (sk_B @ X0)))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ X0)) @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('5', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ (sk_B @ X0)) @ X0)
% 0.20/0.50          | ((X1) = (k2_relat_1 @ (sk_B @ X0)))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ X0)) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.50  thf(t152_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.50  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X0 @ (sk_B @ k1_xboole_0)) @ X0)
% 0.20/0.50          | ((X0) = (k2_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ (sk_B @ X0)) @ X0)
% 0.20/0.50          | ((X1) = (k2_relat_1 @ (sk_B @ X0)))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ X0)) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.50  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) = (k2_relat_1 @ (sk_B @ X0)))
% 0.20/0.50          | (r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('16', plain, (((k1_xboole_0) = (k2_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X0 @ (sk_B @ k1_xboole_0)) @ X0)
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (np__1))
% 0.20/0.50          | ~ (r2_hidden @ X18 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ (sk_B @ k1_xboole_0)))
% 0.20/0.50              = (np__1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ?[C:$i]:
% 0.20/0.50       ( ( ![D:$i]:
% 0.20/0.50           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.50         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_1 @ X14 @ X15)) = (X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.50  thf('21', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X19)
% 0.20/0.50          | ~ (v1_funct_1 @ X19)
% 0.20/0.50          | ((X20) = (X19))
% 0.20/0.50          | ((k1_relat_1 @ X19) != (sk_A))
% 0.20/0.50          | ((k1_relat_1 @ X20) != (sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (v1_relat_1 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ((X1) = (sk_B @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ((X1) = (sk_B @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X1 : $i]:
% 0.20/0.50         (((X1) = (sk_B @ sk_A))
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.50          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_1 @ X14 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_1 @ X14 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.50  thf('32', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X0 @ (sk_B @ k1_xboole_0)) @ X0)
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (sk_C_1 @ X14 @ X15) @ X16) = (X14))
% 0.20/0.50          | ~ (r2_hidden @ X16 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ 
% 0.20/0.50              (sk_C @ X0 @ (sk_B @ k1_xboole_0))) = (X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ (sk_B @ k1_xboole_0)))
% 0.20/0.50            = (X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '35'])).
% 0.20/0.50  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ (sk_B @ k1_xboole_0)))
% 0.20/0.50           = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, (![X0 : $i]: (((np__1) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('43', plain, (((np__1) != (np__1))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '41', '42'])).
% 0.20/0.50  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
