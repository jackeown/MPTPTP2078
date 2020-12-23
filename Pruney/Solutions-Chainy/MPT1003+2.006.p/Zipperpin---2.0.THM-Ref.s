%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qAV7rsy2Ss

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 121 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  568 (1518 expanded)
%              Number of equality atoms :   53 ( 155 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t51_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_funct_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ( r1_tarski @ X17 @ ( k8_relset_1 @ X18 @ X20 @ X19 @ ( k7_relset_1 @ X18 @ X20 @ X19 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('11',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0 ) @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0 )
          = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) ) @ sk_A )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('48',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qAV7rsy2Ss
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 153 iterations in 0.070s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.54  thf(t51_funct_2, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.54         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.22/0.54           ( A ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.54            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.22/0.54              ( A ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t50_funct_2, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54       ( ( r1_tarski @ C @ A ) =>
% 0.22/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.22/0.54           ( r1_tarski @
% 0.22/0.54             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X17 @ X18)
% 0.22/0.54          | ((X20) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_funct_1 @ X19)
% 0.22/0.54          | ~ (v1_funct_2 @ X19 @ X18 @ X20)
% 0.22/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 0.22/0.54          | (r1_tarski @ X17 @ 
% 0.22/0.54             (k8_relset_1 @ X18 @ X20 @ X19 @ 
% 0.22/0.54              (k7_relset_1 @ X18 @ X20 @ X19 @ X17))))),
% 0.22/0.54      inference('cnf', [status(esa)], [t50_funct_2])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ X0 @ 
% 0.22/0.54           (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54            (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)))
% 0.22/0.54          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.22/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.54          | ((sk_B) = (k1_xboole_0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ X0 @ 
% 0.22/0.54           (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54            (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)))
% 0.22/0.54          | ((sk_B) = (k1_xboole_0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.54  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54         (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) != (sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ 
% 0.22/0.54          (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) != (sk_A)))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ 
% 0.22/0.54          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ k1_xboole_0))
% 0.22/0.54          != (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k8_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.22/0.54          | (m1_subset_1 @ (k8_relset_1 @ X14 @ X15 @ X13 @ X16) @ 
% 0.22/0.54             (k1_zfmisc_1 @ X14)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 0.22/0.54          (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i]:
% 0.22/0.54         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0) @ sk_A))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['17', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0) @ 
% 0.22/0.54           k1_xboole_0))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf(d3_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('27', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X7 : $i, X9 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf(t5_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.54          | ~ (v1_xboole_0 @ X12)
% 0.22/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i]:
% 0.22/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.22/0.54           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['25', '34'])).
% 0.22/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.54  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ X0) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '37'])).
% 0.22/0.54  thf('39', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.54  thf('40', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('split', [status(esa)], ['8'])).
% 0.22/0.54  thf('41', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['9', '41'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ X0 @ 
% 0.22/0.54           (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54            (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['7', '42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((r1_tarski @ sk_A @ 
% 0.22/0.54        (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54         (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '43'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i]:
% 0.22/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      ((~ (r1_tarski @ 
% 0.22/0.54           (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54            (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) @ 
% 0.22/0.54           sk_A)
% 0.22/0.54        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54            (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54         (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ 
% 0.22/0.54         (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)) != (sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('50', plain, ($false),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
