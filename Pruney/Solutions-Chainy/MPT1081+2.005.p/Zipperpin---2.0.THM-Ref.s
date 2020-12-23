%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x14aAf4Eyi

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  91 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  466 ( 920 expanded)
%              Number of equality atoms :   17 (  45 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X12 @ X13 @ X14 ) @ X12 )
      | ( m1_funct_2 @ X12 @ X14 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 )
      | ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D_1 @ X12 @ X13 @ X14 ) @ X14 @ X13 )
      | ~ ( v1_funct_1 @ ( sk_D_1 @ X12 @ X13 @ X14 ) )
      | ( m1_funct_2 @ X12 @ X14 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( m1_funct_2 @ ( k1_tarski @ X0 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
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
      | ~ ( v1_funct_1 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 @ X2 ) )
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
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_funct_2 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_funct_2 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( m1_funct_2 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_C ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('29',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x14aAf4Eyi
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:04:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 57 iterations in 0.063s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(m1_funct_2_type, type, m1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(t198_funct_2, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.51       ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.51          ( m1_funct_2 @ ( k1_tarski @ C ) @ A @ B ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t198_funct_2])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d13_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.51       ( ( m1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.51         ( ![D:$i]:
% 0.22/0.51           ( ( m1_subset_1 @ D @ C ) =>
% 0.22/0.51             ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.51               ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (sk_D_1 @ X12 @ X13 @ X14) @ X12)
% 0.22/0.51          | (m1_funct_2 @ X12 @ X14 @ X13)
% 0.22/0.51          | (v1_xboole_0 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.22/0.51  thf(t2_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         ((r2_hidden @ X10 @ X11)
% 0.22/0.51          | (v1_xboole_0 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X0)
% 0.22/0.51          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.51          | (v1_xboole_0 @ X0)
% 0.22/0.51          | (r2_hidden @ (sk_D_1 @ X0 @ X2 @ X1) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_D_1 @ X0 @ X2 @ X1) @ X0)
% 0.22/0.51          | (m1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.51          | (v1_xboole_0 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('5', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(d2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.51       ( ![D:$i]:
% 0.22/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.51          | ((X4) = (X3))
% 0.22/0.51          | ((X4) = (X0))
% 0.22/0.51          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (((X4) = (X0))
% 0.22/0.51          | ((X4) = (X3))
% 0.22/0.51          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.22/0.51          | ((sk_D_1 @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '9'])).
% 0.22/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.51  thf('11', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((sk_D_1 @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.22/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((sk_D_1 @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.22/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((sk_D_1 @ (k1_tarski @ X0) @ X2 @ X1) = (X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2))),
% 0.22/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ (sk_D_1 @ X12 @ X13 @ X14) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.22/0.51          | ~ (v1_funct_2 @ (sk_D_1 @ X12 @ X13 @ X14) @ X14 @ X13)
% 0.22/0.51          | ~ (v1_funct_1 @ (sk_D_1 @ X12 @ X13 @ X14))
% 0.22/0.51          | (m1_funct_2 @ X12 @ X14 @ X13)
% 0.22/0.51          | (v1_xboole_0 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d13_funct_2])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | ~ (v1_funct_1 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2))
% 0.22/0.51          | ~ (v1_funct_2 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_funct_2 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2) @ X2 @ X1)
% 0.22/0.51          | ~ (v1_funct_1 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2))
% 0.22/0.51          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | ~ (v1_funct_1 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_funct_1 @ (sk_D_1 @ (k1_tarski @ X0) @ X1 @ X2))
% 0.22/0.51          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X2 @ X1)
% 0.22/0.51          | ~ (v1_funct_2 @ X0 @ X2 @ X1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_funct_1 @ X0)
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.22/0.51          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.51          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.51          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.51          | (m1_funct_2 @ (k1_tarski @ X0) @ X1 @ X2)
% 0.22/0.51          | ~ (v1_funct_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | (m1_funct_2 @ (k1_tarski @ sk_C) @ sk_A @ sk_B)
% 0.22/0.51        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '21'])).
% 0.22/0.51  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((m1_funct_2 @ (k1_tarski @ sk_C) @ sk_A @ sk_B)
% 0.22/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.51  thf('26', plain, (~ (m1_funct_2 @ (k1_tarski @ sk_C) @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v1_xboole_0 @ (k1_tarski @ sk_C))),
% 0.22/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.51  thf('29', plain, ($false), inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
