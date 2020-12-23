%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMCaQaP7ED

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:08 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 137 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  335 (1265 expanded)
%              Number of equality atoms :    6 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C_2 )
      | ( r2_hidden @ X14 @ sk_B )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('17',plain,
    ( ( sk_C_2 = sk_B )
    | ( r2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('21',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_B )
      | ( r2_hidden @ X14 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('35',plain,(
    ~ ( r2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMCaQaP7ED
% 0.14/0.38  % Computer   : n002.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 16:09:37 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 107 iterations in 0.085s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.58  thf(d3_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf(t44_setfam_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58           ( ( ![D:$i]:
% 0.39/0.58               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.39/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58          ( ![C:$i]:
% 0.39/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58              ( ( ![D:$i]:
% 0.39/0.58                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.39/0.58                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('3', plain, ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | (r2_hidden @ X0 @ X2)
% 0.39/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.58  thf(t1_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.39/0.58          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ sk_C_2)
% 0.39/0.58          | (r2_hidden @ X14 @ sk_B)
% 0.39/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B)
% 0.39/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B) | (r1_tarski @ sk_C_2 @ X0))),
% 0.39/0.58      inference('clc', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.39/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.58  thf(d8_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.39/0.58       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X4 : $i, X6 : $i]:
% 0.39/0.58         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.39/0.58  thf('17', plain, ((((sk_C_2) = (sk_B)) | (r2_xboole_0 @ sk_C_2 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain, (((sk_B) != (sk_C_2))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(t6_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.39/0.58          ( ![C:$i]:
% 0.39/0.58            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (r2_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.39/0.58  thf('21', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('24', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | (r2_hidden @ X0 @ X2)
% 0.39/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ sk_B)
% 0.39/0.58          | (r2_hidden @ X14 @ sk_C_2)
% 0.39/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)
% 0.39/0.58        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf('32', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('33', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_C_2)),
% 0.39/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (r2_xboole_0 @ X7 @ X8) | ~ (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.39/0.58  thf('35', plain, (~ (r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.43/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
