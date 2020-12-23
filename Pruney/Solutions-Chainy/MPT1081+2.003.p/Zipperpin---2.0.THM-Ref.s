%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lfu7VReKg3

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  78 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  425 ( 797 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X8 @ X9 @ X10 ) @ X8 )
      | ( m1_funct_2 @ X8 @ X10 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
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

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X8 @ X9 @ X10 ) @ X10 @ X9 )
      | ~ ( v1_funct_1 @ ( sk_D @ X8 @ X9 @ X10 ) )
      | ( m1_funct_2 @ X8 @ X10 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('26',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lfu7VReKg3
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 38 iterations in 0.024s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(t198_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50          ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t198_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d13_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.50         ( ![D:$i]:
% 0.21/0.50           ( ( m1_subset_1 @ D @ C ) =>
% 0.21/0.50             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (sk_D @ X8 @ X9 @ X10) @ X8)
% 0.21/0.50          | (m1_funct_2 @ X8 @ X10 @ X9)
% 0.21/0.50          | (v1_xboole_0 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         ((r2_hidden @ X6 @ X7)
% 0.21/0.50          | (v1_xboole_0 @ X7)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X0)
% 0.21/0.50          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.50          | (v1_xboole_0 @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.50          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.50          | (v1_xboole_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.50  thf(d1_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X3 : $i]:
% 0.21/0.50         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.50          | ((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.50  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.50  thf('8', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.50      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.50      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.50      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ (sk_D @ X8 @ X9 @ X10) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.21/0.50          | ~ (v1_funct_2 @ (sk_D @ X8 @ X9 @ X10) @ X10 @ X9)
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_D @ X8 @ X9 @ X10))
% 0.21/0.50          | (m1_funct_2 @ X8 @ X10 @ X9)
% 0.21/0.50          | (v1_xboole_0 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.50          | ~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.50          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.50          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ X2 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.50          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.50          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50        | (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '18'])).
% 0.21/0.50  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.50  thf('23', plain, (~ (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((v1_xboole_0 @ (k1_tarski @ sk_C_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.50  thf('26', plain, ($false), inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
