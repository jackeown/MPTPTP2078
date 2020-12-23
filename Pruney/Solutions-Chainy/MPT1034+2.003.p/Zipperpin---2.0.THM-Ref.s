%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fIDx9Uf69c

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 371 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  542 (6582 expanded)
%              Number of equality atoms :   25 (  83 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t143_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( v1_partfun1 @ X8 @ X9 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X14 = X11 )
      | ~ ( r1_partfun1 @ X14 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_partfun1 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( X0 = sk_C )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( v1_partfun1 @ X8 @ X9 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( r2_relset_1 @ X5 @ X6 @ X4 @ X7 )
      | ( X4 != X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_relset_1 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['0','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0 = sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0 = sk_C )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    k1_xboole_0 = sk_C ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['33','35'])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['48','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fIDx9Uf69c
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 66 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.49  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(t143_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49           ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.49            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49              ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t143_funct_2])).
% 0.20/0.49  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc5_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.49             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.20/0.49          | (v1_partfun1 @ X8 @ X9)
% 0.20/0.49          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | (v1_xboole_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.49        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t148_partfun1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.20/0.49               ( r1_partfun1 @ C @ D ) ) =>
% 0.20/0.49             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.49          | ((X14) = (X11))
% 0.20/0.49          | ~ (r1_partfun1 @ X14 @ X11)
% 0.20/0.49          | ~ (v1_partfun1 @ X11 @ X12)
% 0.20/0.49          | ~ (v1_partfun1 @ X14 @ X12)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.49          | ~ (v1_funct_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.49          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.49          | ((X0) = (sk_C))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.49          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.49          | ((X0) = (sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ((X0) = (sk_C))
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.20/0.49        | ((sk_B) = (sk_C))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.49  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.49        | ((sk_B) = (sk_C))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.20/0.49          | (v1_partfun1 @ X8 @ X9)
% 0.20/0.49          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | (v1_xboole_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.49        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.49  thf('24', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc4_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.49           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.20/0.49          | (v1_xboole_0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.20/0.49  thf('27', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, ((((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('30', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.20/0.49          | (r2_relset_1 @ X5 @ X6 @ X4 @ X7)
% 0.20/0.49          | ((X4) != (X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((r2_relset_1 @ X5 @ X6 @ X7 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.49  thf('36', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.49  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.49  thf('38', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '37'])).
% 0.20/0.49  thf('39', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.49  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.49  thf('41', plain, (((v1_xboole_0 @ sk_A) | ((k1_xboole_0) = (sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.20/0.49          | (v1_xboole_0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.20/0.49  thf('44', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((((k1_xboole_0) = (sk_C)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('47', plain, (((k1_xboole_0) = (sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '47'])).
% 0.20/0.49  thf('49', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.49  thf('50', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.49  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.49  thf('52', plain, ((r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.49  thf('53', plain, ($false), inference('demod', [status(thm)], ['48', '52'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
