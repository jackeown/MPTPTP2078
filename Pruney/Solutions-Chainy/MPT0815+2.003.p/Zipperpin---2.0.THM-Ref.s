%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWZmEZ93lD

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  203 ( 263 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t8_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ D ) )
     => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ D ) )
       => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 @ ( k4_tarski @ X1 @ sk_C ) @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ sk_C @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['1','5'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X16 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWZmEZ93lD
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:51:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 48 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(t8_relset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.20/0.49       ( m1_subset_1 @
% 0.20/0.49         ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.20/0.49         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.20/0.49          ( m1_subset_1 @
% 0.20/0.49            ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.20/0.49            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t8_relset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.20/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, ((r2_hidden @ sk_C @ sk_D_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d2_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ?[E:$i,F:$i]:
% 0.20/0.49             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.49               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.49       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.49         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X5)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ X3)
% 0.20/0.49          | ((X2) != (k4_tarski @ X0 @ X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X5)
% 0.20/0.49          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ sk_C @ X1 @ (k4_tarski @ X1 @ sk_C) @ sk_D_1 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((zip_tseitin_0 @ sk_C @ sk_A @ (k4_tarski @ sk_A @ sk_C) @ sk_D_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.49          | (r2_hidden @ X8 @ X11)
% 0.20/0.49          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((r2_hidden @ (k4_tarski @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.49  thf(t63_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k1_tarski @ X16) @ (k1_zfmisc_1 @ X17))
% 0.20/0.49          | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
