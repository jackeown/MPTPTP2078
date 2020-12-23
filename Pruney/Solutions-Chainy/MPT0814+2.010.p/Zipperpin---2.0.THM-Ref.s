%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD5TCxlxii

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  72 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  292 ( 752 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_B )
      | ~ ( r2_hidden @ X20 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD5TCxlxii
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 44 iterations in 0.056s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(t6_relset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.51       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.51            ( ![E:$i,F:$i]:
% 0.20/0.51              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.51                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.51          ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.51               ( ![E:$i,F:$i]:
% 0.20/0.51                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.20/0.51                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.20/0.51  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(l3_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X16 @ X17)
% 0.20/0.51          | (r2_hidden @ X16 @ X18)
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf(d2_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ?[E:$i,F:$i]:
% 0.20/0.51             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.51               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.51       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.51         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.51          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.20/0.51             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.20/0.51          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.20/0.51           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.51        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (((X2) = (k4_tarski @ X0 @ X1))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((sk_A)
% 0.20/0.51         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.51            (sk_F_1 @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.51        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ X4) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('12', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X19 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ X20 @ sk_C)
% 0.20/0.51          | ((sk_A) != (k4_tarski @ X19 @ X20)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_A) != (k4_tarski @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ X0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((sk_A) != (sk_A))
% 0.20/0.51        | ~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.20/0.51        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('18', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, (((sk_A) != (sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.51  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
