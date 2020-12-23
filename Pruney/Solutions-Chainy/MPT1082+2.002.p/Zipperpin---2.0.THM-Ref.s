%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZMSlZMP50

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  390 ( 587 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X3 @ X4 ) @ X2 )
      | ( m1_funct_2 @ X2 @ X4 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
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

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k1_funct_2 @ X9 @ X10 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( r2_hidden @ X8 @ ( k1_funct_2 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X3 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X2 @ X3 @ X4 ) @ X4 @ X3 )
      | ~ ( v1_funct_1 @ ( sk_D @ X2 @ X3 @ X4 ) )
      | ( m1_funct_2 @ X2 @ X4 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X8 @ ( k1_funct_2 @ X9 @ X10 ) ) ) ),
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

thf(fc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_funct_2 @ X6 @ X7 ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_funct_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( m1_funct_2 @ ( k1_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZMSlZMP50
% 0.13/0.36  % Computer   : n004.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:05:09 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 19 iterations in 0.018s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(t199_funct_2, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.48       ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.48          ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t199_funct_2])).
% 0.22/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d13_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.48       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.48         ( ![D:$i]:
% 0.22/0.48           ( ( m1_subset_1 @ D @ C ) =>
% 0.22/0.48             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.48               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (sk_D @ X2 @ X3 @ X4) @ X2)
% 0.22/0.48          | (m1_funct_2 @ X2 @ X4 @ X3)
% 0.22/0.48          | (v1_xboole_0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.22/0.48  thf(t2_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r2_hidden @ X0 @ X1)
% 0.22/0.48          | (v1_xboole_0 @ X1)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X0)
% 0.22/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | (v1_xboole_0 @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.22/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf(t121_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.22/0.48       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         ((v1_funct_2 @ X8 @ X9 @ X10)
% 0.22/0.48          | ~ (r2_hidden @ X8 @ (k1_funct_2 @ X9 @ X10)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.22/0.48          | (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2) @ X1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.22/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.22/0.48          | ~ (r2_hidden @ X8 @ (k1_funct_2 @ X9 @ X10)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.22/0.48          | (m1_subset_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (sk_D @ X2 @ X3 @ X4) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X3)))
% 0.22/0.48          | ~ (v1_funct_2 @ (sk_D @ X2 @ X3 @ X4) @ X4 @ X3)
% 0.22/0.48          | ~ (v1_funct_1 @ (sk_D @ X2 @ X3 @ X4))
% 0.22/0.48          | (m1_funct_2 @ X2 @ X4 @ X3)
% 0.22/0.48          | (v1_xboole_0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.22/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.22/0.48          | ~ (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1) @ X1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_funct_2 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1) @ X1 @ X0)
% 0.22/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X0 @ X1))
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.22/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         ((v1_funct_1 @ X8) | ~ (r2_hidden @ X8 @ (k1_funct_2 @ X9 @ X10)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_funct_2 @ X1 @ X0))
% 0.22/0.48          | (m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X2 @ X3)
% 0.22/0.48          | (v1_funct_1 @ (sk_D @ (k1_funct_2 @ X1 @ X0) @ X3 @ X2)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0)
% 0.22/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X1 @ X0)))),
% 0.22/0.48      inference('clc', [status(thm)], ['14', '17'])).
% 0.22/0.48  thf(fc1_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.48       ( ~( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (v1_xboole_0 @ (k1_funct_2 @ X6 @ X7)) | (v1_xboole_0 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_funct_2])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((m1_funct_2 @ (k1_funct_2 @ X1 @ X0) @ X1 @ X0) | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, (~ (m1_funct_2 @ (k1_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain, ((v1_xboole_0 @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
