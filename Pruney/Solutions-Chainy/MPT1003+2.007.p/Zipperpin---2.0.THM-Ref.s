%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4vwdm5r5wT

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  545 (1402 expanded)
%              Number of equality atoms :   51 ( 148 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X19 ) ) )
      | ( r1_tarski @ X16 @ ( k8_relset_1 @ X17 @ X19 @ X18 @ ( k7_relset_1 @ X17 @ X19 @ X18 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 ) ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('11',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) )
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
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X9 @ X10 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('24',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X1 @ ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r2_hidden @ X1 @ ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X12 @ X13 @ X14 @ X15 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4vwdm5r5wT
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 115 iterations in 0.097s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.55  thf(t51_funct_2, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.55         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.36/0.55           ( A ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.55            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.36/0.55              ( A ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t50_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r1_tarski @ C @ A ) =>
% 0.36/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.36/0.55           ( r1_tarski @
% 0.36/0.55             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X16 @ X17)
% 0.36/0.55          | ((X19) = (k1_xboole_0))
% 0.36/0.55          | ~ (v1_funct_1 @ X18)
% 0.36/0.55          | ~ (v1_funct_2 @ X18 @ X17 @ X19)
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X19)))
% 0.36/0.55          | (r1_tarski @ X16 @ 
% 0.36/0.55             (k8_relset_1 @ X17 @ X19 @ X18 @ 
% 0.36/0.55              (k7_relset_1 @ X17 @ X19 @ X18 @ X16))))),
% 0.36/0.55      inference('cnf', [status(esa)], [t50_funct_2])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r1_tarski @ X0 @ 
% 0.36/0.55           (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55            (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r1_tarski @ X0 @ 
% 0.36/0.55           (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55            (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0)))
% 0.36/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.55  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55         (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) != (sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ 
% 0.36/0.55          (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) != (sk_A)))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ 
% 0.36/0.55          (k7_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ k1_xboole_0))
% 0.36/0.55          != (k1_xboole_0)))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.36/0.55  thf(t7_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (((m1_subset_1 @ sk_C @ 
% 0.36/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf(dt_k8_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.36/0.55          | (m1_subset_1 @ (k8_relset_1 @ X9 @ X10 @ X8 @ X11) @ 
% 0.36/0.55             (k1_zfmisc_1 @ X9)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          (m1_subset_1 @ (k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0) @ 
% 0.36/0.55           (k1_zfmisc_1 @ k1_xboole_0)))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf(t5_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ X6)
% 0.36/0.55          | ~ (v1_xboole_0 @ X7)
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      ((![X0 : $i, X1 : $i]:
% 0.36/0.55          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.55           | ~ (r2_hidden @ X1 @ 
% 0.36/0.55                (k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0))))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.55  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      ((![X0 : $i, X1 : $i]:
% 0.36/0.55          ~ (r2_hidden @ X1 @ (k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0)))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          ((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0) = (k1_xboole_0)))
% 0.36/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '27'])).
% 0.36/0.55  thf('29', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('31', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['9', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r1_tarski @ X0 @ 
% 0.36/0.55           (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55            (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['7', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      ((r1_tarski @ sk_A @ 
% 0.36/0.55        (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55         (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X2 : $i, X4 : $i]:
% 0.36/0.55         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((~ (r1_tarski @ 
% 0.36/0.55           (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55            (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) @ 
% 0.36/0.55           sk_A)
% 0.36/0.55        | ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55            (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t47_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.55         ((r1_tarski @ (k8_relset_1 @ X12 @ X13 @ X14 @ X15) @ X12)
% 0.36/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.55          | ~ (v1_funct_1 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ sk_C)
% 0.36/0.55          | (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55         (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['36', '41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ 
% 0.36/0.55         (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_A)) != (sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
