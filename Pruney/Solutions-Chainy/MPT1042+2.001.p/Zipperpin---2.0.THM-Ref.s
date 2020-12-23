%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhSWVeW4AO

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 227 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  444 (3677 expanded)
%              Number of equality atoms :    7 (  42 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(t158_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
           => ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k5_partfun1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X10 @ X11 @ X12 ) @ X15 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k5_partfun1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X10 @ X11 @ X12 ) @ X15 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','8'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X4 = X5 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,
    ( ( sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v1_partfun1 @ X4 @ X7 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v1_funct_1 @ X4 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['17','20','23'])).

thf('25',plain,
    ( $false
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['28','31','32'])).

thf('34',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['25','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhSWVeW4AO
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:51:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 34 iterations in 0.020s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.22/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.22/0.49  thf(t158_funct_2, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.22/0.49           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.49          ( ![D:$i]:
% 0.22/0.49            ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.22/0.49              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.49                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t158_funct_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (v1_funct_1 @ sk_D)
% 0.22/0.49        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.22/0.49        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))
% 0.22/0.49         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain, ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d7_partfun1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.49         ( v1_funct_1 @ C ) ) =>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.22/0.49           ( ![E:$i]:
% 0.22/0.49             ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.49               ( ?[F:$i]:
% 0.22/0.49                 ( ( v1_funct_1 @ F ) & 
% 0.22/0.49                   ( m1_subset_1 @
% 0.22/0.49                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.49                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.22/0.49                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_2, axiom,
% 0.22/0.49    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.22/0.49       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.22/0.49         ( ( F ) = ( E ) ) & 
% 0.22/0.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.49         ( v1_funct_1 @ F ) ) ))).
% 0.22/0.49  thf(zf_stmt_3, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.22/0.49           ( ![E:$i]:
% 0.22/0.49             ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.49               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.49         (((X14) != (k5_partfun1 @ X12 @ X11 @ X10))
% 0.22/0.49          | (zip_tseitin_0 @ (sk_F_1 @ X15 @ X10 @ X11 @ X12) @ X15 @ X10 @ 
% 0.22/0.49             X11 @ X12)
% 0.22/0.49          | ~ (r2_hidden @ X15 @ X14)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.22/0.49          | ~ (v1_funct_1 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X15 : $i]:
% 0.22/0.49         (~ (v1_funct_1 @ X10)
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.22/0.49          | ~ (r2_hidden @ X15 @ (k5_partfun1 @ X12 @ X11 @ X10))
% 0.22/0.49          | (zip_tseitin_0 @ (sk_F_1 @ X15 @ X10 @ X11 @ X12) @ X15 @ X10 @ 
% 0.22/0.49             X11 @ X12))),
% 0.22/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ sk_B @ sk_A) @ X0 @ sk_C @ 
% 0.22/0.49           sk_B @ sk_A)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.49          | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.49  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ sk_B @ sk_A) @ X0 @ sk_C @ 
% 0.22/0.49           sk_B @ sk_A)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((zip_tseitin_0 @ (sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D @ sk_C @ 
% 0.22/0.49        sk_B @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((zip_tseitin_0 @ (sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D @ sk_C @ 
% 0.22/0.49        sk_B @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (((X4) = (X5)) | ~ (zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('12', plain, (((sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) = (sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain, ((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.22/0.49          | ~ (zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf(cc1_funct_2, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.22/0.49         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_funct_1 @ X0)
% 0.22/0.49          | ~ (v1_partfun1 @ X0 @ X1)
% 0.22/0.49          | (v1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (((v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.22/0.49        | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.22/0.49        | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain, ((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         ((v1_partfun1 @ X4 @ X7) | ~ (zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('20', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, ((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         ((v1_funct_1 @ X4) | ~ (zip_tseitin_0 @ X4 @ X5 @ X3 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '20', '23'])).
% 0.22/0.49  thf('25', plain, (($false) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '24'])).
% 0.22/0.49  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('27', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('28', plain, (((v1_funct_1 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.22/0.49         <= (~
% 0.22/0.49             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_B)) | 
% 0.22/0.49       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.22/0.49       ~ ((v1_funct_1 @ sk_D))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('33', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['28', '31', '32'])).
% 0.22/0.49  thf('34', plain, ($false),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['25', '33'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
