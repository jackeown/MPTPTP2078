%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.liTDtVsPgY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:57 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 326 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  485 (4222 expanded)
%              Number of equality atoms :   42 ( 202 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X7: $i] :
      ( zip_tseitin_0 @ X7 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 )
      | ( zip_tseitin_1 @ X14 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9
       != ( k1_relset_1 @ X9 @ X10 @ X11 ) )
      | ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( zip_tseitin_1 @ X11 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['8','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( v1_funct_2 @ X14 @ X13 @ X12 )
      | ( X14 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['8','24'])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('45',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','30','46'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['26','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.liTDtVsPgY
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.55  % Solved by: fo/fo7.sh
% 0.39/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.55  % done 126 iterations in 0.107s
% 0.39/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.55  % SZS output start Refutation
% 0.39/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.55  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.55  thf(t8_boole, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.39/0.55  thf('1', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]:
% 0.39/0.55         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.39/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.39/0.55  thf('2', plain,
% 0.39/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.55  thf(d1_funct_2, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_0, axiom,
% 0.39/0.55    (![B:$i,A:$i]:
% 0.39/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.55  thf('3', plain,
% 0.39/0.55      (![X7 : $i, X8 : $i]:
% 0.39/0.55         ((zip_tseitin_0 @ X7 @ X8) | ((X8) != (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('4', plain, (![X7 : $i]: (zip_tseitin_0 @ X7 @ k1_xboole_0)),
% 0.39/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.39/0.55  thf('5', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['2', '4'])).
% 0.39/0.55  thf(t130_funct_2, conjecture,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.55       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.55         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_1, negated_conjecture,
% 0.39/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.55        ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.55          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.55            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.55              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.39/0.55    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.39/0.55  thf('6', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.55  thf(zf_stmt_3, axiom,
% 0.39/0.55    (![C:$i,B:$i,A:$i]:
% 0.39/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.55  thf(zf_stmt_5, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.55  thf('7', plain,
% 0.39/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.55         (~ (zip_tseitin_0 @ X12 @ X13)
% 0.39/0.55          | (zip_tseitin_1 @ X14 @ X12 @ X13)
% 0.39/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.55  thf('8', plain,
% 0.39/0.55      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.55  thf('9', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('10', plain,
% 0.39/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.55         (((X9) != (k1_relset_1 @ X9 @ X10 @ X11))
% 0.39/0.55          | (v1_funct_2 @ X11 @ X9 @ X10)
% 0.39/0.55          | ~ (zip_tseitin_1 @ X11 @ X10 @ X9))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.55  thf('11', plain,
% 0.39/0.55      ((((sk_A) != (sk_A))
% 0.39/0.55        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.39/0.55        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.39/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.55  thf('12', plain,
% 0.39/0.55      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.55        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.39/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.55  thf('13', plain,
% 0.39/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('14', plain,
% 0.39/0.55      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.39/0.55         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.39/0.55      inference('split', [status(esa)], ['13'])).
% 0.39/0.55  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('16', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.39/0.55      inference('split', [status(esa)], ['13'])).
% 0.39/0.55  thf('17', plain, (((v1_funct_1 @ sk_C))),
% 0.39/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.55  thf('18', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('19', plain,
% 0.39/0.55      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.39/0.55         <= (~
% 0.39/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.39/0.55      inference('split', [status(esa)], ['13'])).
% 0.39/0.55  thf('20', plain,
% 0.39/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.55  thf('21', plain,
% 0.39/0.55      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.39/0.55       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.39/0.55       ~ ((v1_funct_1 @ sk_C))),
% 0.39/0.55      inference('split', [status(esa)], ['13'])).
% 0.39/0.55  thf('22', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.39/0.55      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.39/0.55  thf('23', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.55      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.39/0.55  thf('24', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.39/0.55      inference('clc', [status(thm)], ['12', '23'])).
% 0.39/0.55  thf('25', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.55      inference('clc', [status(thm)], ['8', '24'])).
% 0.39/0.55  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.55      inference('sup-', [status(thm)], ['5', '25'])).
% 0.39/0.55  thf('27', plain,
% 0.39/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.55         (((X12) != (k1_xboole_0))
% 0.39/0.55          | ((X13) = (k1_xboole_0))
% 0.39/0.55          | (v1_funct_2 @ X14 @ X13 @ X12)
% 0.39/0.55          | ((X14) != (k1_xboole_0))
% 0.39/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.55  thf('28', plain,
% 0.39/0.55      (![X13 : $i]:
% 0.39/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.39/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ k1_xboole_0)))
% 0.39/0.55          | (v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0)
% 0.39/0.55          | ((X13) = (k1_xboole_0)))),
% 0.39/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.55  thf(t113_zfmisc_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.55  thf('29', plain,
% 0.39/0.55      (![X3 : $i, X4 : $i]:
% 0.39/0.55         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.55  thf('30', plain,
% 0.39/0.55      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.55  thf('31', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('32', plain,
% 0.39/0.55      (![X7 : $i, X8 : $i]:
% 0.39/0.55         ((zip_tseitin_0 @ X7 @ X8) | ((X7) = (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('33', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.55      inference('clc', [status(thm)], ['8', '24'])).
% 0.39/0.55  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.55  thf('35', plain,
% 0.39/0.55      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.55  thf('36', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.55      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.39/0.55  thf('37', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf(cc1_subset_1, axiom,
% 0.39/0.55    (![A:$i]:
% 0.39/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.39/0.55       ( ![B:$i]:
% 0.39/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.39/0.55  thf('38', plain,
% 0.39/0.55      (![X5 : $i, X6 : $i]:
% 0.39/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.55          | (v1_xboole_0 @ X5)
% 0.39/0.55          | ~ (v1_xboole_0 @ X6))),
% 0.39/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.39/0.55  thf('39', plain,
% 0.39/0.55      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.39/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.55  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.55  thf('41', plain,
% 0.39/0.55      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.55  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.55  thf('43', plain, ((v1_xboole_0 @ sk_C)),
% 0.39/0.55      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.39/0.55  thf('44', plain,
% 0.39/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.55  thf('45', plain, (((k1_xboole_0) = (sk_C))),
% 0.39/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.55  thf('46', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.55      inference('demod', [status(thm)], ['36', '45'])).
% 0.39/0.55  thf('47', plain,
% 0.39/0.55      (![X13 : $i]:
% 0.39/0.55         ((v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0)
% 0.39/0.55          | ((X13) = (k1_xboole_0)))),
% 0.39/0.55      inference('demod', [status(thm)], ['28', '30', '46'])).
% 0.39/0.55  thf('48', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.55      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.39/0.55  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.55  thf('50', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.39/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.55  thf('51', plain, (((k1_xboole_0) = (sk_C))),
% 0.39/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.55  thf('52', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.39/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.55  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['47', '52'])).
% 0.39/0.55  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.55  thf('55', plain, ($false),
% 0.39/0.55      inference('demod', [status(thm)], ['26', '53', '54'])).
% 0.39/0.55  
% 0.39/0.55  % SZS output end Refutation
% 0.39/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
