%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MFjvMWpwjo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 331 expanded)
%              Number of leaves         :   28 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  491 (4216 expanded)
%              Number of equality atoms :   33 ( 175 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( zip_tseitin_0 @ X9 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,(
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

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['15','18','19'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('28',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ( X16 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['24','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MFjvMWpwjo
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 140 iterations in 0.097s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(l13_xboole_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf(d1_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, axiom,
% 0.20/0.55    (![B:$i,A:$i]:
% 0.20/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X9 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain, (![X9 : $i]: (zip_tseitin_0 @ X9 @ k1_xboole_0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.55  thf(t130_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.55         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.55            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_3, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.20/0.55          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.55         (((X11) != (k1_relset_1 @ X11 @ X12 @ X13))
% 0.20/0.55          | (v1_funct_2 @ X13 @ X11 @ X12)
% 0.20/0.55          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((((sk_A) != (sk_A))
% 0.20/0.55        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.20/0.55        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.55        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.20/0.55         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('14', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('15', plain, (((v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (~
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.20/0.55       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.20/0.55       ~ ((v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('20', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['15', '18', '19'])).
% 0.20/0.55  thf('21', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.20/0.55  thf('22', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['10', '21'])).
% 0.20/0.55  thf('23', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['6', '22'])).
% 0.20/0.55  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('27', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['6', '22'])).
% 0.20/0.55  thf('28', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.55  thf(fc3_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf(cc1_subset_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.55          | (v1_xboole_0 @ X7)
% 0.20/0.55          | ~ (v1_xboole_0 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('34', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.55  thf('35', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('36', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.55  thf('37', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf(t69_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.55          | ~ (r1_tarski @ X3 @ X4)
% 0.20/0.55          | (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.55  thf('41', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['34', '35', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('43', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (((X14) != (k1_xboole_0))
% 0.20/0.55          | ((X15) = (k1_xboole_0))
% 0.20/0.55          | (v1_funct_2 @ X16 @ X15 @ X14)
% 0.20/0.55          | ((X16) != (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X15 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ k1_xboole_0)))
% 0.20/0.55          | (v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0)
% 0.20/0.55          | ((X15) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((((sk_A) = (k1_xboole_0))
% 0.20/0.55        | (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.55  thf('48', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.20/0.55  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('50', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('52', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('clc', [status(thm)], ['47', '52'])).
% 0.20/0.55  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.55  thf('55', plain, ($false),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '53', '54'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
