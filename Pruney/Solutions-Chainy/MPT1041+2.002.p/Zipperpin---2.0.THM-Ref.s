%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yDkJwPYftl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 665 expanded)
%              Number of leaves         :   20 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  633 (12192 expanded)
%              Number of equality atoms :   29 ( 191 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t156_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X0 @ X3 @ X5 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ( X1 != X2 )
      | ~ ( v1_partfun1 @ X1 @ X5 )
      | ~ ( r1_partfun1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( r1_partfun1 @ X0 @ X2 )
      | ~ ( v1_partfun1 @ X2 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k5_partfun1 @ X9 @ X8 @ X7 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X13 @ ( k5_partfun1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ sk_C @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_C @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','25','26'])).

thf('28',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ k1_xboole_0 @ X15 )
      | ( v1_partfun1 @ X16 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','46'])).

thf('48',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    r2_hidden @ sk_C @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['27','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yDkJwPYftl
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 51 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(t156_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48           ( ( r1_partfun1 @ B @ C ) =>
% 0.20/0.48             ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48              ( ( r1_partfun1 @ B @ C ) =>
% 0.20/0.48                ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t156_funct_2])).
% 0.20/0.48  thf('0', plain, (~ (r2_hidden @ sk_C @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t132_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (((X15) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.20/0.48          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.20/0.48          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.20/0.48          | ~ (v1_funct_1 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.20/0.48          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.48  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d7_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.20/0.48           ( ![E:$i]:
% 0.20/0.48             ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48               ( ?[F:$i]:
% 0.20/0.48                 ( ( v1_funct_1 @ F ) & 
% 0.20/0.48                   ( m1_subset_1 @
% 0.20/0.48                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.20/0.48                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, axiom,
% 0.20/0.48    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.20/0.48       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.20/0.48         ( ( F ) = ( E ) ) & 
% 0.20/0.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_funct_1 @ F ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X1 @ X2 @ X0 @ X3 @ X5)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.20/0.48          | ((X1) != (X2))
% 0.20/0.48          | ~ (v1_partfun1 @ X1 @ X5)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.48         (~ (r1_partfun1 @ X0 @ X2)
% 0.20/0.48          | ~ (v1_partfun1 @ X2 @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.20/0.48          | ~ (v1_funct_1 @ X2)
% 0.20/0.48          | (zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5))),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.48  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.48          | (zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A @ sk_A)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.20/0.48           ( ![E:$i]:
% 0.20/0.48             ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         (((X11) != (k5_partfun1 @ X9 @ X8 @ X7))
% 0.20/0.48          | (r2_hidden @ X13 @ X11)
% 0.20/0.48          | ~ (zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.20/0.48          | ~ (v1_funct_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9)
% 0.20/0.48          | (r2_hidden @ X13 @ (k5_partfun1 @ X9 @ X8 @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.48  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))
% 0.20/0.48        | (r2_hidden @ sk_C @ (k5_partfun1 @ sk_A @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.48  thf('24', plain, (~ (r2_hidden @ sk_C @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (~ (r2_hidden @ sk_C @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '25', '26'])).
% 0.20/0.48  thf('28', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (((X17) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.20/0.48          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.20/0.48          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.20/0.48          | ~ (v1_funct_1 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (v1_funct_2 @ X16 @ k1_xboole_0 @ X15)
% 0.20/0.48          | (v1_partfun1 @ X16 @ k1_xboole_0)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X15)))
% 0.20/0.48          | ~ (v1_funct_1 @ X16))),
% 0.20/0.48      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.48  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('45', plain, ((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.48  thf('46', plain, ((v1_partfun1 @ sk_C @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '41', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((r2_hidden @ sk_C @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '54'])).
% 0.20/0.48  thf('56', plain, ($false), inference('demod', [status(thm)], ['27', '55'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
