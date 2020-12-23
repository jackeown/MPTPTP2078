%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.51Oc8T8BiI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  94 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  446 ( 921 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X10 @ X11 @ X12 ) @ X10 )
      | ( m1_funct_2 @ X10 @ X12 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
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
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X10 @ X11 @ X12 ) @ X12 @ X11 )
      | ~ ( v1_funct_1 @ ( sk_D @ X10 @ X11 @ X12 ) )
      | ( m1_funct_2 @ X10 @ X12 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( m1_funct_2 @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('29',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.51Oc8T8BiI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 54 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(t198_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48          ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t198_funct_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d13_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.48       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.48         ( ![D:$i]:
% 0.21/0.48           ( ( m1_subset_1 @ D @ C ) =>
% 0.21/0.48             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.48               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (sk_D @ X10 @ X11 @ X12) @ X10)
% 0.21/0.48          | (m1_funct_2 @ X10 @ X12 @ X11)
% 0.21/0.48          | (v1_xboole_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.48  thf(t2_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ X8 @ X9)
% 0.21/0.48          | (v1_xboole_0 @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X0)
% 0.21/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.48          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X3 : $i, X6 : $i]:
% 0.21/0.48         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.48          | ((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('9', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('11', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ (sk_D @ X10 @ X11 @ X12) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.21/0.48          | ~ (v1_funct_2 @ (sk_D @ X10 @ X11 @ X12) @ X12 @ X11)
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_D @ X10 @ X11 @ X12))
% 0.21/0.48          | (m1_funct_2 @ X10 @ X12 @ X11)
% 0.21/0.48          | (v1_xboole_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.48          | ~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_funct_2 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.48          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X2))
% 0.21/0.48          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.21/0.48          | ~ (v1_funct_2 @ X0 @ X2 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ X0)
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.48          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.48          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.21/0.48          | ~ (v1_funct_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ sk_C_1)
% 0.21/0.48        | (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B_1)
% 0.21/0.48        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.21/0.48        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.48  thf('23', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B_1)
% 0.21/0.48        | (v1_xboole_0 @ (k1_tarski @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.48  thf('26', plain, (~ (m1_funct_2 @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, ((v1_xboole_0 @ (k1_tarski @ sk_C_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('29', plain, ($false), inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
