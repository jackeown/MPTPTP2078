%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2csPb5mLOn

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:11 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 245 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  545 (4456 expanded)
%              Number of equality atoms :   34 (  58 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( v1_partfun1 @ X9 @ X10 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X15 = X12 )
      | ~ ( r1_partfun1 @ X15 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_partfun1 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( v1_partfun1 @ X9 @ X10 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = sk_C )
    | ( sk_A = sk_B )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_A = sk_B )
    | ( sk_B = sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,
    ( ( sk_B = sk_C )
    | ( sk_A = sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = sk_C )
    | ( sk_B = sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    sk_B = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( r2_relset_1 @ X6 @ X7 @ X5 @ X8 )
      | ( X5 != X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_relset_1 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2csPb5mLOn
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 107 iterations in 0.112s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.55  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(t143_funct_2, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.55             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.55           ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.55            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.55          ( ![C:$i]:
% 0.36/0.55            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.55                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.55              ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t143_funct_2])).
% 0.36/0.55  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc5_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.36/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.36/0.55          | (v1_partfun1 @ X9 @ X10)
% 0.36/0.55          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.36/0.55          | ~ (v1_funct_1 @ X9)
% 0.36/0.55          | (v1_xboole_0 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A)
% 0.36/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.36/0.55        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('7', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t148_partfun1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.36/0.55               ( r1_partfun1 @ C @ D ) ) =>
% 0.36/0.55             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ X12)
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.55          | ((X15) = (X12))
% 0.36/0.55          | ~ (r1_partfun1 @ X15 @ X12)
% 0.36/0.55          | ~ (v1_partfun1 @ X12 @ X13)
% 0.36/0.55          | ~ (v1_partfun1 @ X15 @ X13)
% 0.36/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.55          | ~ (v1_funct_1 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.55          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.36/0.55          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.36/0.55          | ((X0) = (sk_C))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.55          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.36/0.55          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.36/0.55          | ((X0) = (sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ sk_A)
% 0.36/0.55          | ((X0) = (sk_C))
% 0.36/0.55          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.36/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.55          | ~ (v1_funct_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((~ (v1_funct_1 @ sk_B)
% 0.36/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.36/0.55        | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.36/0.55        | ((sk_B) = (sk_C))
% 0.36/0.55        | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '13'])).
% 0.36/0.55  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('16', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      ((~ (v1_partfun1 @ sk_B @ sk_A)
% 0.36/0.55        | ((sk_B) = (sk_C))
% 0.36/0.55        | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.36/0.55          | (v1_partfun1 @ X9 @ X10)
% 0.36/0.55          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.36/0.55          | ~ (v1_funct_1 @ X9)
% 0.36/0.55          | (v1_xboole_0 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A)
% 0.36/0.55        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.55        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('22', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.55  thf('24', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc4_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.55           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X2)
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.36/0.55          | (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.55  thf('27', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf('28', plain, ((((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['24', '27'])).
% 0.36/0.55  thf('29', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.55  thf(t8_boole, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i]: (((sk_B) = (sk_C)) | ((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      ((((sk_B) = (sk_C)) | ((sk_A) = (sk_B)) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.36/0.55  thf('33', plain, ((((sk_A) = (sk_B)) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.55  thf('34', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X2)
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.36/0.55          | (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.55  thf('37', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, ((((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i]: (((sk_B) = (sk_C)) | ((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((((sk_B) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.55  thf('41', plain, ((((sk_A) = (sk_C)) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((((sk_B) = (sk_C)) | ((sk_B) = (sk_C)) | ((sk_B) = (sk_C)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['33', '41'])).
% 0.36/0.55  thf('43', plain, (((sk_B) = (sk_C))),
% 0.36/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.36/0.55          | (r2_relset_1 @ X6 @ X7 @ X5 @ X8)
% 0.36/0.55          | ((X5) != (X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((r2_relset_1 @ X6 @ X7 @ X8 @ X8)
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.55  thf('47', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '46'])).
% 0.36/0.55  thf('48', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '43', '47'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
