%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u858fffRKd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  442 ( 865 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t198_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t198_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X15 @ X16 @ X17 ) @ X15 )
      | ( m1_funct_2 @ X15 @ X17 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X15 @ X16 @ X17 ) @ X17 @ X16 )
      | ~ ( v1_funct_1 @ ( sk_D @ X15 @ X16 @ X17 ) )
      | ( m1_funct_2 @ X15 @ X17 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u858fffRKd
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 114 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(t198_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53          ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t198_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d13_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.53       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.53         ( ![D:$i]:
% 0.21/0.53           ( ( m1_subset_1 @ D @ C ) =>
% 0.21/0.53             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.53               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (sk_D @ X15 @ X16 @ X17) @ X15)
% 0.21/0.53          | (m1_funct_2 @ X15 @ X17 @ X16)
% 0.21/0.53          | (v1_xboole_0 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.53  thf(t2_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((r2_hidden @ X13 @ X14)
% 0.21/0.53          | (v1_xboole_0 @ X14)
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X0)
% 0.21/0.53          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.53          | (v1_xboole_0 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.53          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.53          | (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X3 : $i]:
% 0.21/0.53         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.53          | ((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('8', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(fc3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.21/0.53  thf('10', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.53      inference('clc', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.53      inference('clc', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.53      inference('clc', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ (sk_D @ X15 @ X16 @ X17) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.21/0.53          | ~ (v1_funct_2 @ (sk_D @ X15 @ X16 @ X17) @ X17 @ X16)
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_D @ X15 @ X16 @ X17))
% 0.21/0.53          | (m1_funct_2 @ X15 @ X17 @ X16)
% 0.21/0.53          | (v1_xboole_0 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.53          | ~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1)
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.53          | ~ (v1_funct_2 @ X0 @ X2 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.53          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.53          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.53          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.53          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.53          | ~ (v1_funct_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((~ (v1_funct_1 @ sk_C_1)
% 0.21/0.53        | (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)
% 0.21/0.53        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '20'])).
% 0.21/0.53  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (((m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)
% 0.21/0.53        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.53  thf('25', plain, (~ (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, ((v1_xboole_0 @ (k1_tarski @ sk_C_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('28', plain, ($false), inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
