%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUbn3CMUFZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  309 ( 803 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ( X15
       != ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_A @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
        = ( k4_tarski @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_A @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( r2_hidden @ X24 @ sk_C_1 )
      | ( sk_A
       != ( k4_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_A @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUbn3CMUFZ
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 50 iterations in 0.025s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.47  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.47  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(t6_relset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.47       ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.47            ( ![E:$i,F:$i]:
% 0.21/0.47              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.47                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.47          ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.47               ( ![E:$i,F:$i]:
% 0.21/0.47                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.21/0.47                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.21/0.47  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i]:
% 0.21/0.47         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('3', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.47  thf(d2_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47           ( ?[E:$i,F:$i]:
% 0.21/0.47             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.47               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.47       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.47         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.47          | (zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.21/0.47             (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.21/0.47          | ((X15) != (k2_zfmisc_1 @ X14 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.21/0.47           (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.21/0.47          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.21/0.47        (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_A @ sk_C_1 @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (((X6) = (k4_tarski @ X4 @ X5))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((sk_A)
% 0.21/0.47         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.21/0.47            (sk_F_1 @ sk_A @ sk_C_1 @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.21/0.47        (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_A @ sk_C_1 @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('14', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X23 : $i, X24 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X23 @ sk_B)
% 0.21/0.47          | ~ (r2_hidden @ X24 @ sk_C_1)
% 0.21/0.47          | ((sk_A) != (k4_tarski @ X23 @ X24)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) != (k4_tarski @ (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((sk_A) != (sk_A))
% 0.21/0.47        | ~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.21/0.47        (sk_E_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_A @ sk_C_1 @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('20', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, (((sk_A) != (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.47  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
