%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9XgTdz0ZUY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  86 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  478 (1267 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t115_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X10
        = ( k1_funct_1 @ X11 @ ( sk_F @ X10 @ X11 @ X12 @ X13 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k7_relset_1 @ X13 @ X14 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_F @ X10 @ X11 @ X12 @ X13 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k7_relset_1 @ X13 @ X14 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X15: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D @ X15 ) )
      | ~ ( r2_hidden @ X15 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X15 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_F @ X10 @ X11 @ X12 @ X13 ) @ X13 )
      | ~ ( r2_hidden @ X10 @ ( k7_relset_1 @ X13 @ X14 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['18','24'])).

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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9XgTdz0ZUY
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 69 iterations in 0.059s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.55  thf(t116_funct_2, conjecture,
% 0.38/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.55       ( ![E:$i]:
% 0.38/0.55         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.38/0.55              ( ![F:$i]:
% 0.38/0.55                ( ( m1_subset_1 @ F @ A ) =>
% 0.38/0.55                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.38/0.55                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.55          ( ![E:$i]:
% 0.38/0.55            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.38/0.55                 ( ![F:$i]:
% 0.38/0.55                   ( ( m1_subset_1 @ F @ A ) =>
% 0.38/0.55                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.38/0.55                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t115_funct_2, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.55       ( ![E:$i]:
% 0.38/0.55         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.38/0.55              ( ![F:$i]:
% 0.38/0.55                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.38/0.55                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.55         (((X10) = (k1_funct_1 @ X11 @ (sk_F @ X10 @ X11 @ X12 @ X13)))
% 0.38/0.55          | ~ (r2_hidden @ X10 @ (k7_relset_1 @ X13 @ X14 @ X11 @ X12))
% 0.38/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.55          | ~ (v1_funct_2 @ X11 @ X13 @ X14)
% 0.38/0.55          | ~ (v1_funct_1 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_funct_1 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.38/0.55          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | ((X1) = (k1_funct_1 @ sk_D @ (sk_F @ X1 @ sk_D @ X0 @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | ((X1) = (k1_funct_1 @ sk_D @ (sk_F @ X1 @ sk_D @ X0 @ sk_A))))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (((sk_E) = (k1_funct_1 @ sk_D @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '6'])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.55         ((r2_hidden @ (sk_F @ X10 @ X11 @ X12 @ X13) @ X12)
% 0.38/0.55          | ~ (r2_hidden @ X10 @ (k7_relset_1 @ X13 @ X14 @ X11 @ X12))
% 0.38/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.55          | ~ (v1_funct_2 @ X11 @ X13 @ X14)
% 0.38/0.55          | ~ (v1_funct_1 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_funct_1 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.38/0.55          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      ((r2_hidden @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_C_1)),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X15 : $i]:
% 0.38/0.55         (((sk_E) != (k1_funct_1 @ sk_D @ X15))
% 0.38/0.55          | ~ (r2_hidden @ X15 @ sk_C_1)
% 0.38/0.55          | ~ (m1_subset_1 @ X15 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      ((~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)
% 0.38/0.55        | ((sk_E) != (k1_funct_1 @ sk_D @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.55         ((r2_hidden @ (sk_F @ X10 @ X11 @ X12 @ X13) @ X13)
% 0.38/0.55          | ~ (r2_hidden @ X10 @ (k7_relset_1 @ X13 @ X14 @ X11 @ X12))
% 0.38/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.55          | ~ (v1_funct_2 @ X11 @ X13 @ X14)
% 0.38/0.55          | ~ (v1_funct_1 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_funct_1 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.38/0.55          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.38/0.55          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.38/0.55  thf('25', plain, ((r2_hidden @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '24'])).
% 0.38/0.55  thf(d3_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X1 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X1 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.55  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X4 : $i, X6 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf(t4_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X7 @ X8)
% 0.38/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.38/0.55          | (m1_subset_1 @ X7 @ X9))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['25', '33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (((sk_E) != (k1_funct_1 @ sk_D @ (sk_F @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['17', '34'])).
% 0.38/0.55  thf('36', plain, ($false),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['7', '35'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
