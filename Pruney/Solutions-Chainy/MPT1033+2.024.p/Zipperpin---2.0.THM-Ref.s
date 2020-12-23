%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xieOHyanYX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:07 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 247 expanded)
%              Number of leaves         :   20 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  551 (5026 expanded)
%              Number of equality atoms :   36 ( 248 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
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
      ( ( sk_C = sk_D )
      | ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = sk_D )
    | ( sk_B = sk_C )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_B = sk_C )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_D )
      | ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,
    ( ( sk_C = sk_D )
    | ( sk_B = sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = sk_D )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_C = sk_D )
    | ( sk_C = sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    sk_C = sk_D ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_relset_1 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['45'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xieOHyanYX
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 228 iterations in 0.144s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.43/0.60  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.43/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.60  thf(t142_funct_2, conjecture,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60           ( ( r1_partfun1 @ C @ D ) =>
% 0.43/0.60             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.43/0.60               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60          ( ![D:$i]:
% 0.43/0.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60              ( ( r1_partfun1 @ C @ D ) =>
% 0.43/0.60                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.43/0.60                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.43/0.60  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc5_funct_2, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.43/0.60       ( ![C:$i]:
% 0.43/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.43/0.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.43/0.60  thf('3', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.43/0.60          | (v1_partfun1 @ X9 @ X10)
% 0.43/0.60          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.43/0.60          | ~ (v1_funct_1 @ X9)
% 0.43/0.60          | (v1_xboole_0 @ X11))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (((v1_xboole_0 @ sk_B)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.43/0.60        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.43/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.60  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t148_partfun1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( ( v1_funct_1 @ D ) & 
% 0.43/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.43/0.60               ( r1_partfun1 @ C @ D ) ) =>
% 0.43/0.60             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X12)
% 0.43/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.43/0.60          | ((X15) = (X12))
% 0.43/0.60          | ~ (r1_partfun1 @ X15 @ X12)
% 0.43/0.60          | ~ (v1_partfun1 @ X12 @ X13)
% 0.43/0.60          | ~ (v1_partfun1 @ X15 @ X13)
% 0.43/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.43/0.60          | ~ (v1_funct_1 @ X15))),
% 0.43/0.60      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.43/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.43/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.43/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.43/0.60          | ((X0) = (sk_D))
% 0.43/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.60  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('12', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.43/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.43/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.43/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.43/0.60          | ((X0) = (sk_D)))),
% 0.43/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.60  thf('13', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         ((v1_xboole_0 @ sk_B)
% 0.43/0.60          | ((X0) = (sk_D))
% 0.43/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.43/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.43/0.60          | ~ (v1_funct_1 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.43/0.60  thf('14', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.43/0.60        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.43/0.60        | ((sk_C) = (sk_D))
% 0.43/0.60        | (v1_xboole_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['1', '13'])).
% 0.43/0.60  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.43/0.60        | ((sk_C) = (sk_D))
% 0.43/0.60        | (v1_xboole_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('19', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.43/0.60          | (v1_partfun1 @ X9 @ X10)
% 0.43/0.60          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.43/0.60          | ~ (v1_funct_1 @ X9)
% 0.43/0.60          | (v1_xboole_0 @ X11))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      (((v1_xboole_0 @ sk_B)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.43/0.60        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.43/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.60  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.43/0.60  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc4_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.60       ( ![C:$i]:
% 0.43/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.43/0.60           ( v1_xboole_0 @ C ) ) ) ))).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.60         (~ (v1_xboole_0 @ X2)
% 0.43/0.60          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.43/0.60          | (v1_xboole_0 @ X3))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.43/0.60  thf('27', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.60  thf('28', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['24', '27'])).
% 0.43/0.60  thf('29', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.43/0.60  thf(t8_boole, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.43/0.60  thf('30', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t8_boole])).
% 0.43/0.60  thf('31', plain,
% 0.43/0.60      (![X0 : $i]: (((sk_C) = (sk_D)) | ((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.60  thf('32', plain,
% 0.43/0.60      ((((sk_C) = (sk_D)) | ((sk_B) = (sk_C)) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['28', '31'])).
% 0.43/0.60  thf('33', plain, ((((sk_B) = (sk_C)) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.43/0.60  thf('34', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.43/0.60  thf('35', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('36', plain,
% 0.43/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.60         (~ (v1_xboole_0 @ X2)
% 0.43/0.60          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.43/0.60          | (v1_xboole_0 @ X3))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.43/0.60  thf('37', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.60  thf('38', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['34', '37'])).
% 0.43/0.60  thf('39', plain,
% 0.43/0.60      (![X0 : $i]: (((sk_C) = (sk_D)) | ((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.60  thf('40', plain,
% 0.43/0.60      ((((sk_C) = (sk_D)) | ((sk_B) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.43/0.60  thf('41', plain, ((((sk_B) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.60  thf('42', plain,
% 0.43/0.60      ((((sk_C) = (sk_D)) | ((sk_C) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.43/0.60      inference('sup+', [status(thm)], ['33', '41'])).
% 0.43/0.60  thf('43', plain, (((sk_C) = (sk_D))),
% 0.43/0.60      inference('simplify', [status(thm)], ['42'])).
% 0.43/0.60  thf('44', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(reflexivity_r2_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.43/0.60  thf('45', plain,
% 0.43/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.43/0.60         ((r2_relset_1 @ X5 @ X6 @ X7 @ X7)
% 0.43/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.43/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.43/0.60      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.43/0.60  thf('46', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.43/0.60      inference('condensation', [status(thm)], ['45'])).
% 0.43/0.60  thf('47', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.43/0.60      inference('sup-', [status(thm)], ['44', '46'])).
% 0.43/0.60  thf('48', plain, ($false),
% 0.43/0.60      inference('demod', [status(thm)], ['0', '43', '47'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
