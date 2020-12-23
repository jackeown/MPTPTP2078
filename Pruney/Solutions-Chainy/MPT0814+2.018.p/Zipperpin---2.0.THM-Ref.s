%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAkQ0nuikd

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 558 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( X3
        = ( k4_tarski @ ( sk_E @ X3 @ X2 @ X1 ) @ ( sk_F @ X3 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( X0
        = ( k4_tarski @ ( sk_E @ X0 @ sk_C @ sk_B ) @ ( sk_F @ X0 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ ( sk_F @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X3 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ sk_B )
      | ~ ( r2_hidden @ X8 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_C @ sk_B ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X3 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_C @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAkQ0nuikd
% 0.11/0.34  % Computer   : n009.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 14:38:56 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 16 iterations in 0.012s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(t6_relset_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.19/0.46       ( ~( ( r2_hidden @ A @ D ) & 
% 0.19/0.46            ( ![E:$i,F:$i]:
% 0.19/0.46              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.19/0.46                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.19/0.46          ( ~( ( r2_hidden @ A @ D ) & 
% 0.19/0.46               ( ![E:$i,F:$i]:
% 0.19/0.46                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.19/0.46                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.19/0.46  thf('0', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t3_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf('3', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t103_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.19/0.46          ( r2_hidden @ D @ A ) & 
% 0.19/0.46          ( ![E:$i,F:$i]:
% 0.19/0.46            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.19/0.46                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ X1 @ X2))
% 0.19/0.46          | ((X3) = (k4_tarski @ (sk_E @ X3 @ X2 @ X1) @ (sk_F @ X3 @ X2 @ X1)))
% 0.19/0.46          | ~ (r2_hidden @ X3 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ sk_D)
% 0.19/0.46          | ((X0)
% 0.19/0.46              = (k4_tarski @ (sk_E @ X0 @ sk_C @ sk_B) @ 
% 0.19/0.46                 (sk_F @ X0 @ sk_C @ sk_B))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (((sk_A)
% 0.19/0.46         = (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ 
% 0.19/0.46            (sk_F @ sk_A @ sk_C @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '5'])).
% 0.19/0.46  thf('7', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ X1 @ X2))
% 0.19/0.46          | (r2_hidden @ (sk_E @ X3 @ X2 @ X1) @ X1)
% 0.19/0.46          | ~ (r2_hidden @ X3 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ sk_D)
% 0.19/0.46          | (r2_hidden @ (sk_E @ X0 @ sk_C @ sk_B) @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain, ((r2_hidden @ (sk_E @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X7 @ sk_B)
% 0.19/0.46          | ~ (r2_hidden @ X8 @ sk_C)
% 0.19/0.46          | ((sk_A) != (k4_tarski @ X7 @ X8)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_A) != (k4_tarski @ (sk_E @ sk_A @ sk_C @ sk_B) @ X0))
% 0.19/0.46          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_F @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '13'])).
% 0.19/0.46  thf('15', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ X1 @ X2))
% 0.19/0.46          | (r2_hidden @ (sk_F @ X3 @ X2 @ X1) @ X2)
% 0.19/0.46          | ~ (r2_hidden @ X3 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ sk_D)
% 0.19/0.46          | (r2_hidden @ (sk_F @ X0 @ sk_C @ sk_B) @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf('19', plain, ((r2_hidden @ (sk_F @ sk_A @ sk_C @ sk_B) @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.46  thf('20', plain, (((sk_A) != (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['14', '19'])).
% 0.19/0.46  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
