%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMI8IDDWeO

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  93 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  296 (1156 expanded)
%              Number of equality atoms :   16 (  62 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ X5 @ sk_C_1 )
      | ( r2_hidden @ X5 @ sk_B )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_B = sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ X5 @ sk_B )
      | ( r2_hidden @ X5 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( sk_B = sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('24',plain,(
    sk_B = sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMI8IDDWeO
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 26 iterations in 0.026s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(t2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.48       ( ( A ) = ( B ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((X1) = (X0))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((X1) = (X0))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.48  thf(t44_setfam_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48           ( ( ![D:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.48             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48          ( ![C:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48              ( ( ![D:$i]:
% 0.22/0.48                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.48                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t4_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.48          | (m1_subset_1 @ X2 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 0.22/0.48          | ((X0) = (sk_C_1))
% 0.22/0.48          | (m1_subset_1 @ (sk_C @ sk_C_1 @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X5 @ sk_C_1)
% 0.22/0.48          | (r2_hidden @ X5 @ sk_B)
% 0.22/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((X0) = (sk_C_1))
% 0.22/0.48          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.22/0.48          | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 0.22/0.48          | ((X0) = (sk_C_1))
% 0.22/0.48          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.22/0.48          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 0.22/0.48          | ((X0) = (sk_C_1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.22/0.48          | ((X0) = (sk_C_1))
% 0.22/0.48          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((((sk_B) = (sk_C_1)) | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.22/0.48      inference('eq_fact', [status(thm)], ['9'])).
% 0.22/0.48  thf('11', plain, (((sk_B) != (sk_C_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.48          | (m1_subset_1 @ X2 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X5 @ sk_B)
% 0.22/0.48          | (r2_hidden @ X5 @ sk_C_1)
% 0.22/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.22/0.48        | ~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('20', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((X1) = (X0))
% 0.22/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B) | ((sk_B) = (sk_C_1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('24', plain, (((sk_B) = (sk_C_1))),
% 0.22/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain, (((sk_B) != (sk_C_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
