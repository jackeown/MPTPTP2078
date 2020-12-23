%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dQBAjGOwu8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  444 ( 796 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_tarski @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X21 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dQBAjGOwu8
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 76 iterations in 0.091s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(t61_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.55         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.55            ( m1_subset_1 @
% 0.20/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.55            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.20/0.55  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (k1_relset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((r1_tarski @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.55        (k1_tarski @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d1_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.20/0.55          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.20/0.55          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.55        | ((k1_tarski @ sk_A)
% 0.20/0.55            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![B:$i,A:$i]:
% 0.20/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.20/0.55          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.20/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.55        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((((sk_B) = (k1_xboole_0))
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.55  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '15'])).
% 0.20/0.55  thf('17', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '16'])).
% 0.20/0.55  thf(t69_enumset1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.55  thf('18', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf(t38_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((r2_hidden @ X3 @ X4) | ~ (r1_tarski @ (k2_tarski @ X3 @ X5) @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t7_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X21 @ X22)
% 0.20/0.55          | ((X23) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X24)
% 0.20/0.55          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.20/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ X24 @ X21) @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55          | ((sk_B) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B)
% 0.20/0.55          | ((sk_B) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.55  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '29'])).
% 0.20/0.55  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
