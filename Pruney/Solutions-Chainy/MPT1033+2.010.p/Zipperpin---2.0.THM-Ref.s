%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.loXqvpkgDs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:05 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 253 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  581 (5060 expanded)
%              Number of equality atoms :   38 ( 250 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X16 = X13 )
      | ~ ( r1_partfun1 @ X16 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_partfun1 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
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

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_D )
      | ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C = sk_D )
    | ( sk_B = sk_C )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( sk_B = sk_C )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_D )
      | ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('44',plain,
    ( ( sk_C = sk_D )
    | ( sk_B = sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = sk_D )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_C = sk_D )
    | ( sk_C = sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,(
    sk_C = sk_D ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( r2_relset_1 @ X7 @ X8 @ X6 @ X9 )
      | ( X6 != X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_relset_1 @ X7 @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.loXqvpkgDs
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:57:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 236 iterations in 0.202s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.65  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.44/0.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(t142_funct_2, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ![D:$i]:
% 0.44/0.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65           ( ( r1_partfun1 @ C @ D ) =>
% 0.44/0.65             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.44/0.65               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65          ( ![D:$i]:
% 0.44/0.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65              ( ( r1_partfun1 @ C @ D ) =>
% 0.44/0.65                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.44/0.65                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.44/0.65  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc5_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65       ( ![C:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.44/0.65          | (v1_partfun1 @ X10 @ X11)
% 0.44/0.65          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.44/0.65          | ~ (v1_funct_1 @ X10)
% 0.44/0.65          | (v1_xboole_0 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_D)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.65  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t148_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ![D:$i]:
% 0.44/0.65         ( ( ( v1_funct_1 @ D ) & 
% 0.44/0.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.44/0.65               ( r1_partfun1 @ C @ D ) ) =>
% 0.44/0.65             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X13)
% 0.44/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.44/0.65          | ((X16) = (X13))
% 0.44/0.65          | ~ (r1_partfun1 @ X16 @ X13)
% 0.44/0.65          | ~ (v1_partfun1 @ X13 @ X14)
% 0.44/0.65          | ~ (v1_partfun1 @ X16 @ X14)
% 0.44/0.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.44/0.65          | ~ (v1_funct_1 @ X16))),
% 0.44/0.65      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.65          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.65          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.44/0.65          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.65          | ((X0) = (sk_D))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.65  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.65          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.65          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.44/0.65          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.65          | ((X0) = (sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ sk_B)
% 0.44/0.65          | ((X0) = (sk_D))
% 0.44/0.65          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.65          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['7', '12'])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.44/0.65        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.44/0.65        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.44/0.65        | ((sk_C) = (sk_D))
% 0.44/0.65        | (v1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '13'])).
% 0.44/0.65  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.44/0.65        | ((sk_C) = (sk_D))
% 0.44/0.65        | (v1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.44/0.65          | (v1_partfun1 @ X10 @ X11)
% 0.44/0.65          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.44/0.65          | ~ (v1_funct_1 @ X10)
% 0.44/0.65          | (v1_xboole_0 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.65  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('clc', [status(thm)], ['17', '23'])).
% 0.44/0.65  thf(fc3_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc1_subset_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_xboole_0 @ A ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.44/0.65          | (v1_xboole_0 @ X4)
% 0.44/0.65          | ~ (v1_xboole_0 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('29', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['25', '28'])).
% 0.44/0.65  thf('30', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['24', '29'])).
% 0.44/0.65  thf('31', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('clc', [status(thm)], ['17', '23'])).
% 0.44/0.65  thf(t8_boole, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t8_boole])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X0 : $i]: (((sk_C) = (sk_D)) | ((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      ((((sk_C) = (sk_D)) | ((sk_B) = (sk_C)) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.65  thf('35', plain, ((((sk_B) = (sk_C)) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.65  thf('36', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('clc', [status(thm)], ['17', '23'])).
% 0.44/0.65  thf('37', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.44/0.65          | (v1_xboole_0 @ X4)
% 0.44/0.65          | ~ (v1_xboole_0 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.65  thf('41', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['37', '40'])).
% 0.44/0.65  thf('42', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['36', '41'])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X0 : $i]: (((sk_C) = (sk_D)) | ((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      ((((sk_C) = (sk_D)) | ((sk_B) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain, ((((sk_B) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      ((((sk_C) = (sk_D)) | ((sk_C) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['35', '45'])).
% 0.44/0.65  thf('47', plain, (((sk_C) = (sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_r2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.65  thf('49', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.44/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.44/0.65          | (r2_relset_1 @ X7 @ X8 @ X6 @ X9)
% 0.44/0.65          | ((X6) != (X9)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.44/0.65  thf('50', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         ((r2_relset_1 @ X7 @ X8 @ X9 @ X9)
% 0.44/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.44/0.65  thf('51', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.44/0.65      inference('sup-', [status(thm)], ['48', '50'])).
% 0.44/0.65  thf('52', plain, ($false),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '47', '51'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
