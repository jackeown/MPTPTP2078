%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yS9JjJNaYo

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 ( 604 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t199_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t199_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ( ( m1_funct_2 @ C @ A @ B )
      <=> ! [D: $i] :
            ( ( m1_subset_1 @ D @ C )
           => ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X3 @ X4 @ X5 ) @ X3 )
      | ( m1_funct_2 @ X3 @ X5 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k1_funct_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_funct_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X3 @ X4 @ X5 ) @ X5 @ X4 )
      | ~ ( v1_funct_1 @ ( sk_D @ X3 @ X4 @ X5 ) )
      | ( m1_funct_2 @ X3 @ X5 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ~ ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X9 @ ( k1_funct_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( m1_funct_2 @ ( k1_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_funct_2 @ X7 @ X8 ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_funct_2])).

thf('22',plain,(
    v1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yS9JjJNaYo
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:01:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 26 iterations in 0.019s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(t199_funct_2, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47       ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47          ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t199_funct_2])).
% 0.19/0.47  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d13_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.19/0.47       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.19/0.47         ( ![D:$i]:
% 0.19/0.47           ( ( m1_subset_1 @ D @ C ) =>
% 0.19/0.47             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.47               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (sk_D @ X3 @ X4 @ X5) @ X3)
% 0.19/0.47          | (m1_funct_2 @ X3 @ X5 @ X4)
% 0.19/0.47          | (v1_xboole_0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.19/0.47  thf(d2_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ X1)
% 0.19/0.47          | (r2_hidden @ X0 @ X1)
% 0.19/0.47          | (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0)
% 0.19/0.47          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.19/0.47          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf(t121_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.19/0.47       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         ((v1_funct_2 @ X9 @ X10 @ X11)
% 0.19/0.47          | ~ (r2_hidden @ X9 @ (k1_funct_2 @ X10 @ X11)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.19/0.47          | (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2) @ X1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.19/0.47          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.19/0.47          | ~ (r2_hidden @ X9 @ (k1_funct_2 @ X10 @ X11)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.19/0.47          | (m1_subset_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2) @ 
% 0.19/0.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ (sk_D @ X3 @ X4 @ X5) @ 
% 0.19/0.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.19/0.47          | ~ (v1_funct_2 @ (sk_D @ X3 @ X4 @ X5) @ X5 @ X4)
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_D @ X3 @ X4 @ X5))
% 0.19/0.47          | (m1_funct_2 @ X3 @ X5 @ X4)
% 0.19/0.47          | (v1_xboole_0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.19/0.47          | ~ (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1) @ X1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1) @ X1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.19/0.47          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         ((v1_funct_1 @ X9) | ~ (r2_hidden @ X9 @ (k1_funct_2 @ X10 @ X11)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.19/0.47          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.19/0.47          | (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0)))),
% 0.19/0.47      inference('clc', [status(thm)], ['14', '17'])).
% 0.19/0.47  thf('19', plain, (~ (m1_funct_2 @ (k1_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain, ((v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf(fc1_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47       ( ~( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ (k1_funct_2 @ X7 @ X8)) | (v1_xboole_0 @ X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_funct_2])).
% 0.19/0.47  thf('22', plain, ((v1_xboole_0 @ sk_B)),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
