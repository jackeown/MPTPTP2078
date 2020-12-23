%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdoVLiqscr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 198 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  541 (2331 expanded)
%              Number of equality atoms :   42 ( 137 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('2',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['4','8'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

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

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18
       != ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['13','25','27','28'])).

thf('30',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ( X23 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X22: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('38',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','24'])).

thf('39',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','29'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('45',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('46',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X24: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['31','42','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdoVLiqscr
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 164 iterations in 0.100s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(t130_funct_2, conjecture,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.57       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.22/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.57        ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.57          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.22/0.57            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.57              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc1_funct_2, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.22/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.57         (~ (v1_funct_1 @ X13)
% 0.22/0.57          | ~ (v1_partfun1 @ X13 @ X14)
% 0.22/0.57          | (v1_funct_2 @ X13 @ X14 @ X15)
% 0.22/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.22/0.57        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.22/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.57  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.22/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('8', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.22/0.57      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.57  thf('9', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.22/0.57      inference('clc', [status(thm)], ['4', '8'])).
% 0.22/0.57  thf(t9_mcart_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.57                 ( ![C:$i,D:$i]:
% 0.22/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.57                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X10 : $i]:
% 0.22/0.57         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.22/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t5_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.57          | ~ (v1_xboole_0 @ X9)
% 0.22/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf(d1_funct_2, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_1, axiom,
% 0.22/0.57    (![B:$i,A:$i]:
% 0.22/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.57  thf(zf_stmt_3, axiom,
% 0.22/0.57    (![C:$i,B:$i,A:$i]:
% 0.22/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.57  thf(zf_stmt_5, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.57         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.22/0.57          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.22/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.22/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.57  thf('19', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.57         (((X18) != (k1_relset_1 @ X18 @ X19 @ X20))
% 0.22/0.57          | (v1_funct_2 @ X20 @ X18 @ X19)
% 0.22/0.57          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((sk_A) != (sk_A))
% 0.22/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.22/0.57        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.22/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.57  thf('23', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.22/0.57      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.57  thf('24', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.22/0.57      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf('25', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '24'])).
% 0.22/0.57  thf(t113_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.57  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '25', '27', '28'])).
% 0.22/0.57  thf('30', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '29'])).
% 0.22/0.57  thf('31', plain, (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.57         (((X21) != (k1_xboole_0))
% 0.22/0.57          | ((X22) = (k1_xboole_0))
% 0.22/0.57          | (v1_funct_2 @ X23 @ X22 @ X21)
% 0.22/0.57          | ((X23) != (k1_xboole_0))
% 0.22/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X22 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.22/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ k1_xboole_0)))
% 0.22/0.57          | (v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0)
% 0.22/0.57          | ((X22) = (k1_xboole_0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.57  thf(t4_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (![X22 : $i]:
% 0.22/0.57         ((v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0)
% 0.22/0.57          | ((X22) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.57  thf('37', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.22/0.57      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.57  thf('38', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '24'])).
% 0.22/0.57  thf('39', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.22/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '29'])).
% 0.22/0.57  thf('41', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.22/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.57  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['36', '41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X10 : $i]:
% 0.22/0.57         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.22/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.57  thf(dt_k6_partfun1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( m1_subset_1 @
% 0.22/0.57         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.57       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X25 : $i]:
% 0.22/0.57         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.22/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.57          | ~ (v1_xboole_0 @ X9)
% 0.22/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57          | ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.57  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['43', '50'])).
% 0.22/0.57  thf('52', plain, (![X24 : $i]: (v1_partfun1 @ (k6_partfun1 @ X24) @ X24)),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.22/0.57  thf('53', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('sup+', [status(thm)], ['51', '52'])).
% 0.22/0.57  thf('54', plain, ($false),
% 0.22/0.57      inference('demod', [status(thm)], ['31', '42', '53'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
